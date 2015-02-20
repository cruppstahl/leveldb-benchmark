// Copyright (c) 2011 The LevelDB Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file. See the AUTHORS file for names of contributors.

#include <sys/types.h>
#include <stdio.h>
#include <stdlib.h>
#include "db/db_impl.h"
#include "db/version_set.h"
#include "leveldb/cache.h"
#include "leveldb/db.h"
#include "leveldb/env.h"
#include "leveldb/write_batch.h"
#include "port/port.h"
#include "util/crc32c.h"
#include "util/histogram.h"
#include "util/mutexlock.h"
#include "util/random.h"
#include "util/testutil.h"

#include <ham/hamsterdb.h>
#include <ham/hamsterdb_ola.h>
#include <ham/hamsterdb_int.h> // for ham_is_debug()

static const int kDefault16 = 1; // unlimited binary keys
static const int kPax16     = 2;
static const int kPax8      = 3;

// Comma-separated list of operations to run in the specified order
//   Actual benchmarks:
//      fillseq       -- write N values in sequential key order in async mode
//      fillrandom    -- write N values in random key order in async mode
//      overwrite     -- overwrite N values in random key order in async mode
//      fill100K      -- write N/1000 100K values in random order in async mode
//      deleteseq     -- delete N keys in sequential order
//      deleterandom  -- delete N keys in random order
//      readseq       -- read N times sequentially
//      readreverse   -- read N times in reverse order
//      readrandom    -- read N times in random order
//      readmissing   -- read N missing keys in random order
//      readhot       -- read N times in random order from 1% section of DB
static const char* FLAGS_benchmarks =
    "xx-fillseq_8/8,"
    "xx-readseq_8/8,"
    "xx-sum_8/8,"
    "xx-fillrandom_8/8,"
    "xx-readrandom_8/8,"
    "xx-fillseq_8/100,"
    "xx-readseq_8/100,"
    "xx-fillrandom_8/100,"
    "xx-readrandom_8/100,"
    "xx-fillseq_16/100,"
    "xx-readseq_16/100,"
    "xx-fillrandom_16/100,"
    "xx-readrandom_16/100,"
    "xx-count_if_16/100,"
#if 0
    "fillseq,"
    "readseq,"
    "readhot,"
    "readmissing,"
    "readreverse,"
    "fillrandom,"
    "overwrite,"
    "readrandom,"
    "readrandomsmall,"
    "deleteseq,"
    "fillseq,"
    "deleterandom,"
    "fill100K,"
#endif
    ;

// Number of key/values to place in database
static int FLAGS_num = 1000000;

// Number of read operations to do.  If negative, do FLAGS_num reads.
static int FLAGS_reads = -1;

// Size of each value
static int FLAGS_value_size = 100;

// Size of each key
static int FLAGS_key_size = 16;

// The database configuration - default, pax etc
static int FLAGS_configuration = kDefault16;

// Arrange to generate values that shrink to this fraction of
// their original size after compression
static double FLAGS_compression_ratio = 0.5;

// Print histogram of operation timings
static bool FLAGS_histogram = false;

// Number of bytes to use as a cache of uncompressed data.
// Negative means use default settings.
// leveldb runs with 4 mb
static uint64_t FLAGS_cache_size = 4 * 1024 * 1024;

// If true, do not destroy the existing database.  If you set this
// flag and also specify a benchmark that wants a fresh database, that
// benchmark will fail.
static bool FLAGS_use_existing_db = false;

// Use the db with the following name.
static const char* FLAGS_db = NULL;

namespace leveldb {

namespace {

static ham_bool_t
count_if_predicate(const void *key_data, ham_u16_t key_size, void *context) {
  const char *p = (const char *)key_data; 
  return (key_size >= 2 && memcmp(p + key_size - 2, "77", 2) == 0);
}

// Helper for quickly generating random data.
class RandomGenerator {
 private:
  std::string data_;
  int pos_;

 public:
  RandomGenerator() {
    // We use a limited amount of data over and over again and ensure
    // that it is larger than the compression window (32KB), and also
    // large enough to serve all typical value sizes we want to write.
    Random rnd(301);
    std::string piece;
    while (data_.size() < 1048576) {
      // Add a short fragment that is as compressible as specified
      // by FLAGS_compression_ratio.
      test::CompressibleString(&rnd, FLAGS_compression_ratio, 100, &piece);
      data_.append(piece);
    }
    pos_ = 0;
  }

  Slice Generate(size_t len) {
    if (pos_ + len > data_.size()) {
      pos_ = 0;
      assert(len < data_.size());
    }
    pos_ += len;
    return Slice(data_.data() + pos_ - len, len);
  }
};

static Slice TrimSpace(Slice s) {
  size_t start = 0;
  while (start < s.size() && isspace(s[start])) {
    start++;
  }
  size_t limit = s.size();
  while (limit > start && isspace(s[limit-1])) {
    limit--;
  }
  return Slice(s.data() + start, limit - start);
}

static void AppendWithSpace(std::string* str, Slice msg) {
  if (msg.empty()) return;
  if (!str->empty()) {
    str->push_back(' ');
  }
  str->append(msg.data(), msg.size());
}

class Stats {
 private:
  double start_;
  double finish_;
  double seconds_;
  int done_;
  int next_report_;
  int64_t bytes_;
  double last_op_finish_;
  Histogram hist_;
  std::string message_;

 public:
  Stats() { Start(); }

  void Start() {
    next_report_ = 100;
    last_op_finish_ = start_;
    hist_.Clear();
    done_ = 0;
    bytes_ = 0;
    seconds_ = 0;
    start_ = Env::Default()->NowMicros();
    finish_ = start_;
    message_.clear();
  }

  void Merge(const Stats& other) {
    hist_.Merge(other.hist_);
    done_ += other.done_;
    bytes_ += other.bytes_;
    seconds_ += other.seconds_;
    if (other.start_ < start_) start_ = other.start_;
    if (other.finish_ > finish_) finish_ = other.finish_;

    // Just keep the messages from one thread
    if (message_.empty()) message_ = other.message_;
  }

  void Stop() {
    finish_ = Env::Default()->NowMicros();
    seconds_ = (finish_ - start_) * 1e-6;
  }

  void AddMessage(Slice msg) {
    AppendWithSpace(&message_, msg);
  }

  void FinishedSingleOp() {
    if (FLAGS_histogram) {
      double now = Env::Default()->NowMicros();
      double micros = now - last_op_finish_;
      hist_.Add(micros);
      if (micros > 20000) {
        fprintf(stderr, "long op: %.1f micros%30s\r", micros, "");
        fflush(stderr);
      }
      last_op_finish_ = now;
    }

    done_++;
    if (done_ >= next_report_) {
      if      (next_report_ < 1000)   next_report_ += 100;
      else if (next_report_ < 5000)   next_report_ += 500;
      else if (next_report_ < 10000)  next_report_ += 1000;
      else if (next_report_ < 50000)  next_report_ += 5000;
      else if (next_report_ < 100000) next_report_ += 10000;
      else if (next_report_ < 500000) next_report_ += 50000;
      else                            next_report_ += 100000;
      fprintf(stderr, "... finished %d ops%30s\r", done_, "");
      fflush(stderr);
    }
  }

  void AddBytes(int64_t n) {
    bytes_ += n;
  }

  void Report(const Slice& name) {
    // Pretend at least one op was done in case we are running a benchmark
    // that does not call FinishedSingleOp().
    if (done_ < 1) done_ = 1;

    std::string extra;
    if (bytes_ > 0) {
      // Rate is computed on actual elapsed time, not the sum of per-thread
      // elapsed times.
      double elapsed = (finish_ - start_) * 1e-6;
      char rate[100];
      snprintf(rate, sizeof(rate), "%6.1f MB/s",
               (bytes_ / 1048576.0) / elapsed);
      extra = rate;
    }
    AppendWithSpace(&extra, message_);

    fprintf(stdout, "%-12s : %11.3f micros/op;%s%s\n",
            name.ToString().c_str(),
            seconds_ * 1e6 / done_,
            (extra.empty() ? "" : " "),
            extra.c_str());
    if (FLAGS_histogram) {
      fprintf(stdout, "Microseconds per op:\n%s\n", hist_.ToString().c_str());
    }
    fflush(stdout);
  }
};

// State shared by all concurrent executions of the same benchmark.
struct SharedState {
  port::Mutex mu;
  port::CondVar cv;
  int total;

  // Each thread goes through the following states:
  //    (1) initializing
  //    (2) waiting for others to be initialized
  //    (3) running
  //    (4) done

  int num_initialized;
  int num_done;
  bool start;

  SharedState() : cv(&mu) { }
};

// Per-thread state for concurrent executions of the same benchmark.
struct ThreadState {
  int tid;             // 0..n-1 when running in n threads
  Random rand;         // Has different seeds for different threads
  Stats stats;
  SharedState* shared;

  ThreadState(int index)
      : tid(index),
        rand(1000 + index) {
  }
};

}  // namespace

class Benchmark {
 private:
  ham_env_t *env_;
  ham_db_t *db_;
  int num_;
  int value_size_;
  int key_size_;
  int reads_;

  void PrintHeader() {
    PrintEnvironment();
    fprintf(stdout, "Keys:       %d bytes each\n", FLAGS_key_size);
    fprintf(stdout, "Values:     %d bytes each (%d bytes after compression)\n",
            FLAGS_value_size,
            static_cast<int>(FLAGS_value_size * FLAGS_compression_ratio + 0.5));
    fprintf(stdout, "Entries:    %d\n", num_);
    fprintf(stdout, "RawSize:    %.1f MB (estimated)\n",
            ((static_cast<int64_t>(FLAGS_key_size + FLAGS_value_size) * num_)
             / 1048576.0));
    fprintf(stdout, "FileSize:   %.1f MB (estimated)\n",
            (((FLAGS_key_size + FLAGS_value_size * FLAGS_compression_ratio) * num_)
             / 1048576.0));
    PrintWarnings();
    fprintf(stdout, "------------------------------------------------\n");
  }

  void PrintWarnings() {
    if (ham_is_debug())
      fprintf(stdout,
              "WARNING: hamsterdb debug build is VERY slow\n"
              );
#if defined(__GNUC__) && !defined(__OPTIMIZE__)
    fprintf(stdout,
            "WARNING: Optimization is disabled: benchmarks unnecessarily slow\n"
            );
#endif
#ifndef NDEBUG
    fprintf(stdout,
            "WARNING: Assertions are enabled; benchmarks unnecessarily slow\n");
#endif
  }

  void PrintEnvironment() {
    ham_u32_t maj, min, rev;
    ham_get_version(&maj, &min, &rev);

    fprintf(stderr, "hamsterdb:  version %u.%u.%u\n",
            maj, min, rev);

#if defined(__linux)
    time_t now = time(NULL);
    fprintf(stderr, "Date:       %s", ctime(&now));  // ctime() adds newline

    FILE* cpuinfo = fopen("/proc/cpuinfo", "r");
    if (cpuinfo != NULL) {
      char line[1000];
      int num_cpus = 0;
      std::string cpu_type;
      std::string cache_size;
      while (fgets(line, sizeof(line), cpuinfo) != NULL) {
        const char* sep = strchr(line, ':');
        if (sep == NULL) {
          continue;
        }
        Slice key = TrimSpace(Slice(line, sep - 1 - line));
        Slice val = TrimSpace(Slice(sep + 1));
        if (key == "model name") {
          ++num_cpus;
          cpu_type = val.ToString();
        } else if (key == "cache size") {
          cache_size = val.ToString();
        }
      }
      fclose(cpuinfo);
      fprintf(stderr, "CPU:        %d * %s\n", num_cpus, cpu_type.c_str());
      fprintf(stderr, "CPUCache:   %s\n", cache_size.c_str());
    }
#endif
  }

 public:
  Benchmark()
  : env_(NULL),
    db_(NULL),
    num_(FLAGS_num),
    value_size_(FLAGS_value_size),
    key_size_(FLAGS_key_size),
    reads_(FLAGS_reads < 0 ? FLAGS_num : FLAGS_reads) {
  }

  ~Benchmark() {
    Close();
  }

  void Run() {
    PrintHeader();
    if (FLAGS_use_existing_db)
      Open();
    else
      Create();

    const char* benchmarks = FLAGS_benchmarks;
    while (benchmarks != NULL) {
      const char* sep = strchr(benchmarks, ',');
      Slice name;
      if (sep == NULL) {
        name = benchmarks;
        benchmarks = NULL;
      } else {
        name = Slice(benchmarks, sep - benchmarks);
        benchmarks = sep + 1;
      }

      // Reset parameters that may be overriddden bwlow
      num_ = FLAGS_num;
      reads_ = (FLAGS_reads < 0 ? FLAGS_num : FLAGS_reads);
      value_size_ = FLAGS_value_size;
      key_size_ = FLAGS_key_size;

      void (Benchmark::*method)(ThreadState*) = NULL;
      bool fresh_db = false;

      if (name == Slice("xx-fillseq_8/8")) {
        FLAGS_configuration = kPax8;
        fresh_db = true;
        key_size_ = 8;
        value_size_ = 8;
        method = &Benchmark::WriteSeq;
      } else if (name == Slice("xx-readseq_8/8")) {
        key_size_ = 8;
        value_size_ = 8;
        method = &Benchmark::ReadSequential;
      } else if (name == Slice("xx-sum_8/8")) {
        key_size_ = 8;
        value_size_ = 8;
        method = &Benchmark::CalculateSum;
      } else if (name == Slice("xx-fillrandom_8/8")) {
        FLAGS_configuration = kPax8;
        fresh_db = true;
        key_size_ = 8;
        value_size_ = 8;
        method = &Benchmark::WriteRandom;
      } else if (name == Slice("xx-readrandom_8/8")) {
        key_size_ = 8;
        value_size_ = 8;
        method = &Benchmark::ReadRandom;
      } else if (name == Slice("xx-fillseq_8/100")) {
        FLAGS_configuration = kPax8;
        fresh_db = true;
        key_size_ = 8;
        value_size_ = 100;
        method = &Benchmark::WriteSeq;
      } else if (name == Slice("xx-readseq_8/100")) {
        key_size_ = 8;
        value_size_ = 100;
        method = &Benchmark::ReadSequential;
      } else if (name == Slice("xx-fillrandom_8/100")) {
        FLAGS_configuration = kPax8;
        fresh_db = true;
        key_size_ = 8;
        value_size_ = 100;
        method = &Benchmark::WriteRandom;
      } else if (name == Slice("xx-readrandom_8/100")) {
        key_size_ = 8;
        value_size_ = 100;
        method = &Benchmark::ReadRandom;
      } else if (name == Slice("xx-fillseq_16/100")) {
        FLAGS_configuration = kPax16;
        fresh_db = true;
        key_size_ = 16;
        value_size_ = 100;
        method = &Benchmark::WriteSeq;
      } else if (name == Slice("xx-readseq_16/100")) {
        key_size_ = 16;
        value_size_ = 100;
        method = &Benchmark::ReadSequential;
      } else if (name == Slice("xx-fillrandom_16/100")) {
        FLAGS_configuration = kPax16;
        fresh_db = true;
        key_size_ = 16;
        value_size_ = 100;
        method = &Benchmark::WriteRandom;
      } else if (name == Slice("xx-readrandom_16/100")) {
        key_size_ = 16;
        value_size_ = 100;
        method = &Benchmark::ReadRandom;
      } else if (name == Slice("xx-count_if_16/100")) {
        key_size_ = 16;
        value_size_ = 100;
        method = &Benchmark::CountIf;
      }

      else if (name == Slice("fillseq")) {
        fresh_db = true;
        method = &Benchmark::WriteSeq;
      } else if (name == Slice("fillrandom")) {
        fresh_db = true;
        method = &Benchmark::WriteRandom;
      } else if (name == Slice("overwrite")) {
        fresh_db = false;
        method = &Benchmark::WriteRandom;
      } else if (name == Slice("fill100K")) {
        fresh_db = true;
        num_ /= 1000;
        value_size_ = 100 * 1000;
        method = &Benchmark::WriteRandom;
      } else if (name == Slice("readseq")) {
        method = &Benchmark::ReadSequential;
      } else if (name == Slice("readreverse")) {
        method = &Benchmark::ReadReverse;
      } else if (name == Slice("readrandom")) {
        method = &Benchmark::ReadRandom;
      } else if (name == Slice("readmissing")) {
        method = &Benchmark::ReadMissing;
      } else if (name == Slice("readhot")) {
        method = &Benchmark::ReadHot;
      } else if (name == Slice("readrandomsmall")) {
        reads_ /= 1000;
        method = &Benchmark::ReadRandom;
      } else if (name == Slice("deleteseq")) {
        method = &Benchmark::DeleteSeq;
      } else if (name == Slice("deleterandom")) {
        method = &Benchmark::DeleteRandom;
      } else {
        if (name != Slice()) {  // No error message for empty name
          fprintf(stderr, "unknown benchmark '%s'\n", name.ToString().c_str());
        }
      }

      if (fresh_db) {
        if (FLAGS_use_existing_db) {
          fprintf(stdout, "%-12s : skipped (--use_existing_db is true)\n",
                  name.ToString().c_str());
          method = NULL;
        } else {
          Close();
          Create();
        }
      }

      int num_threads = 1; // hamsterdb is single-threaded
      if (method != NULL) {
        RunBenchmark(num_threads, name, method);
      }
    }
  }

 private:
  struct ThreadArg {
    Benchmark* bm;
    SharedState* shared;
    ThreadState* thread;
    void (Benchmark::*method)(ThreadState*);
  };

  static void ThreadBody(void* v) {
    ThreadArg* arg = reinterpret_cast<ThreadArg*>(v);
    SharedState* shared = arg->shared;
    ThreadState* thread = arg->thread;
    {
      MutexLock l(&shared->mu);
      shared->num_initialized++;
      if (shared->num_initialized >= shared->total) {
        shared->cv.SignalAll();
      }
      while (!shared->start) {
        shared->cv.Wait();
      }
    }

    thread->stats.Start();
    (arg->bm->*(arg->method))(thread);
    thread->stats.Stop();

    {
      MutexLock l(&shared->mu);
      shared->num_done++;
      if (shared->num_done >= shared->total) {
        shared->cv.SignalAll();
      }
    }
  }

  void RunBenchmark(int n, Slice name,
                    void (Benchmark::*method)(ThreadState*)) {
    SharedState shared;
    shared.total = n;
    shared.num_initialized = 0;
    shared.num_done = 0;
    shared.start = false;

    ThreadArg* arg = new ThreadArg[n];
    for (int i = 0; i < n; i++) {
      arg[i].bm = this;
      arg[i].method = method;
      arg[i].shared = &shared;
      arg[i].thread = new ThreadState(i);
      arg[i].thread->shared = &shared;
      Env::Default()->StartThread(ThreadBody, &arg[i]);
    }

    shared.mu.Lock();
    while (shared.num_initialized < n) {
      shared.cv.Wait();
    }

    shared.start = true;
    shared.cv.SignalAll();
    while (shared.num_done < n) {
      shared.cv.Wait();
    }
    shared.mu.Unlock();

    for (int i = 1; i < n; i++) {
      arg[0].thread->stats.Merge(arg[i].thread->stats);
    }
    arg[0].thread->stats.Report(name);

    for (int i = 0; i < n; i++) {
      delete arg[i].thread;
    }
    delete[] arg;
  }

  void Close() {
    ham_status_t st = ham_env_close(env_, HAM_AUTO_CLEANUP);
    if (st)
      printf("Warning: failed to close Environment, error %s\n",
                      ham_strerror(st));
    env_ = NULL;
    db_ = NULL;
  }

  void Open() {
    assert(env_ == NULL);
    assert(db_ == NULL);
    ham_parameter_t env_params[] = {
        {HAM_PARAM_CACHE_SIZE, FLAGS_cache_size},
        {0, 0}
    };

    ham_status_t st = ham_env_open(&env_, FLAGS_db, 0, &env_params[0]);
    if (st) {
      fprintf(stderr, "%d: open error: %s\n", __LINE__, ham_strerror(st));
      exit(1);
    }

    st = ham_env_open_db(env_, &db_, 1, 0, 0);
    if (st) {
      fprintf(stderr, "%d: open error: %s\n", __LINE__, ham_strerror(st));
      exit(1);
    }
  }

  void Create() {
    assert(env_ == NULL);
    assert(db_ == NULL);
    ham_parameter_t env_params[] = {
        {HAM_PARAM_CACHE_SIZE, FLAGS_cache_size},
        {0, 0}
    };

    ham_status_t st = ham_env_create(&env_, FLAGS_db, 0, 0, &env_params[0]);
    if (st) {
      fprintf(stderr, "%d: create error: %s\n", __LINE__, ham_strerror(st));
      exit(1);
    }

    ham_parameter_t db_params[8] = {
        {HAM_PARAM_RECORD_SIZE, (uint64_t)value_size_},
        {0, 0}
    };

    if (FLAGS_configuration == kDefault16) {
      // nop;
    }
    else if (FLAGS_configuration == kPax16) {
      db_params[1].name = HAM_PARAM_KEY_SIZE;
      db_params[1].value = key_size_;
    }
    else if (FLAGS_configuration == kPax8) {
      db_params[1].name = HAM_PARAM_KEY_TYPE;
      db_params[1].value = HAM_TYPE_UINT64;
      db_params[2].name = HAM_PARAM_KEY_SIZE;
      db_params[2].value = key_size_;
    }

    st = ham_env_create_db(env_, &db_, 1, 0, &db_params[0]);
    if (st) {
      fprintf(stderr, "%d: create error: %s\n", __LINE__, ham_strerror(st));
      exit(1);
    }
  }

  void WriteSeq(ThreadState* thread) {
    DoWrite(thread, true);
  }

  void WriteRandom(ThreadState* thread) {
    DoWrite(thread, false);
  }

  void DoWrite(ThreadState* thread, bool seq) {
    if (num_ != FLAGS_num) {
      char msg[100];
      snprintf(msg, sizeof(msg), "(%d ops)", num_);
      thread->stats.AddMessage(msg);
    }

    char buffer[100];
    int64_t bytes = 0;
    RandomGenerator gen;
    ham_key_t key = {0};
    key.size = key_size_;
    key.data = &buffer[0];

    ham_record_t record = {0};
    record.size = value_size_;

    ham_cursor_t *cursor;
    ham_status_t st = ham_cursor_create(&cursor, db_, 0, 0);
    if (st) {
      fprintf(stderr, "failed to create a cursor: %s\n", ham_strerror(st));
      exit(1);
    }

    for (int i = 0; i < num_; i += 1) {
      record.data = (void *)gen.Generate(value_size_).data();
      const int k = seq ? i : (thread->rand.Next() % FLAGS_num);
      GenerateKey(buffer, sizeof(buffer), k);

      st = ham_cursor_insert(cursor, &key, &record,
                      HAM_OVERWRITE | (seq ? HAM_HINT_APPEND : 0));
      if (st) {
        fprintf(stderr, "insert error: %s\n", ham_strerror(st));
        exit(1);
      }

      bytes += value_size_ + key_size_;
      thread->stats.FinishedSingleOp();
    }

    ham_cursor_close(cursor);

    thread->stats.AddBytes(bytes);
  }

  void GenerateKey(char *buffer, size_t buffer_size, int k) {
    if (key_size_ == 16)
      snprintf(buffer, buffer_size, "%016d", k);
    else if (key_size_ == 8)
      *(ham_u64_t *)buffer = (ham_u64_t)k;
    else {
      fprintf(stderr, "Invalid key size %d, only 8 or 16 are supported\n",
                      key_size_);
      exit(1);
    }
  }

  void GenerateMissingKey(char *buffer, size_t buffer_size, int k) {
    if (key_size_ == 16)
      snprintf(buffer, buffer_size, "%016d.", k);
    else if (key_size_ == 8)
      *(ham_u64_t *)buffer = ((ham_u64_t)k) | 0x80000000ull;
    else {
      fprintf(stderr, "Invalid key size %d, only 8 or 16 are supported\n",
                      key_size_);
      exit(1);
    }
  }

  void ReadSequential(ThreadState* thread) {
    int64_t bytes = 0;

    ham_cursor_t *cursor;
    ham_status_t st = ham_cursor_create(&cursor, db_, 0, 0);
    if (st) {
      fprintf(stderr, "failed to create a cursor: %s\n", ham_strerror(st));
      exit(1);
    }

    ham_key_t key = {0};
    ham_record_t record = {0};
    int i = 0;
    while (0 == ham_cursor_move(cursor, &key, &record, HAM_CURSOR_NEXT)) {
      bytes += key.size + record.size;
      thread->stats.FinishedSingleOp();
      i++;
    }

    if (i != reads_) {
      fprintf(stderr, "not enough reads!");
      exit(1);
    }

    ham_cursor_close(cursor);
    thread->stats.AddBytes(bytes);
  }

  void CalculateSum(ThreadState* thread) {
    hola_result_t result = {0};
    ham_status_t st = hola_sum(db_, 0, &result);
    if (st) {
      fprintf(stderr, "hola_sum failed: %s\n", ham_strerror(st));
      exit(1);
    }
    thread->stats.FinishedSingleOp();
    char msg[100];
    snprintf(msg, sizeof(msg), "(sum is %lu)", result.u.result_u64);
    thread->stats.AddMessage(msg);
  }

  void CountIf(ThreadState* thread) {
    hola_result_t result = {0};
    hola_bool_predicate_t predicate;
    predicate.context = 0;
    predicate.predicate_func = count_if_predicate;

    ham_status_t st = hola_count_if(db_, 0, &predicate, &result);
    thread->stats.FinishedSingleOp();
    if (st) {
      fprintf(stderr, "hola_count_if failed: %s\n", ham_strerror(st));
      exit(1);
    }
    char msg[100];
    snprintf(msg, sizeof(msg), "(count is %lu)", result.u.result_u64);
    thread->stats.AddMessage(msg);
  }

  void ReadReverse(ThreadState* thread) {
    int64_t bytes = 0;

    ham_cursor_t *cursor;
    ham_status_t st = ham_cursor_create(&cursor, db_, 0, 0);
    if (st) {
      fprintf(stderr, "failed to create a cursor: %s\n", ham_strerror(st));
      exit(1);
    }

    ham_key_t key = {0};
    ham_record_t record = {0};
    int i = 0;
    while (0 == ham_cursor_move(cursor, &key, &record, HAM_CURSOR_PREVIOUS)) {
      bytes += key.size + record.size;
      thread->stats.FinishedSingleOp();
      i++;
    }

    if (i != reads_) {
      fprintf(stderr, "not enough reads!");
      exit(1);
    }

    ham_cursor_close(cursor);
    thread->stats.AddBytes(bytes);
  }

  void ReadRandom(ThreadState* thread) {
    int found = 0;
    char buffer[100];
    ham_key_t key = {0};
    key.size = key_size_;
    key.data = &buffer[0];

    ham_record_t record = {0};

    for (int i = 0; i < reads_; i++) {
      const int k = thread->rand.Next() % FLAGS_num;
      GenerateKey(buffer, sizeof(buffer), k);

      ham_status_t st = ham_db_find(db_, 0, &key, &record, 0);
      if (st == 0) {
        found++;
      }
      else if (st != HAM_KEY_NOT_FOUND) {
        fprintf(stderr, "find failed: %s\n", ham_strerror(st));
        exit(1);
      }
      thread->stats.FinishedSingleOp();
    }

    char msg[100];
    snprintf(msg, sizeof(msg), "(%d of %d found)", found, num_);
    thread->stats.AddMessage(msg);
  }

  void ReadMissing(ThreadState* thread) {
    char buffer[100];
    ham_key_t key = {0};
    key.size = key_size_;
    key.data = &buffer[0];

    ham_record_t record = {0};

    for (int i = 0; i < reads_; i++) {
      const int k = thread->rand.Next() % FLAGS_num;
      GenerateMissingKey(buffer, sizeof(buffer), k);

      ham_status_t st = ham_db_find(db_, 0, &key, &record, 0);
      if (st && st != HAM_KEY_NOT_FOUND) {
        fprintf(stderr, "find failed: %s\n", ham_strerror(st));
        exit(1);
      }
      thread->stats.FinishedSingleOp();
    }
  }

  void ReadHot(ThreadState* thread) {
    char buffer[100];
    ham_key_t key = {0};
    key.size = key_size_;
    key.data = &buffer[0];

    ham_record_t record = {0};

    const int range = (FLAGS_num + 99) / 100;

    for (int i = 0; i < reads_; i++) {
      const int k = thread->rand.Next() % range;
      GenerateKey(buffer, sizeof(buffer), k);

      ham_status_t st = ham_db_find(db_, 0, &key, &record, 0);
      if (st && st != HAM_KEY_NOT_FOUND) {
        fprintf(stderr, "find failed: %s\n", ham_strerror(st));
        exit(1);
      }
      thread->stats.FinishedSingleOp();
    }
  }

  void DoDelete(ThreadState* thread, bool seq) {
    char buffer[100];
    ham_key_t key = {0};
    key.size = key_size_;
    key.data = &buffer[0];

    for (int i = 0; i < reads_; i++) {
      const int k = seq ? i : (thread->rand.Next() % FLAGS_num);
      GenerateKey(buffer, sizeof(buffer), k);

      ham_status_t st = ham_db_erase(db_, 0, &key, 0);
      if (st && st != HAM_KEY_NOT_FOUND) {
        fprintf(stderr, "erase failed: %s\n", ham_strerror(st));
        exit(1);
      }
      thread->stats.FinishedSingleOp();
    }
  }

  void DeleteSeq(ThreadState* thread) {
    DoDelete(thread, true);
  }

  void DeleteRandom(ThreadState* thread) {
    DoDelete(thread, false);
  }
};

}  // namespace leveldb

int main(int argc, char** argv) {
  std::string default_db_path;

  for (int i = 1; i < argc; i++) {
    double d;
    int n;
    char junk;
    if (leveldb::Slice(argv[i]).starts_with("--help")) {
      printf("leveldb benchmark, adjusted for hamsterdb; options:\n"
             "  --benchmarks=foo1,foo2,...   specifies benchmarks to run\n"
             "  --num=<N>                    tests with N keys\n"
             "  --cache_size=<N>             size of the cache (default: 4m)\n"
             "  --value_size=<N>             size of the records\n"
             "  --configuration=<cfg>        selects a configuration\n"
             "      def16       default btree layout, 16 byte binary keys\n"
             "      pax16       pax btree layout, 16 byte binary keys\n"
             "      pax8        pax btree layout, 8 byte uint64 keys\n");
      exit(0);
    } else if (leveldb::Slice(argv[i]).starts_with("--benchmarks=")) {
      FLAGS_benchmarks = argv[i] + strlen("--benchmarks=");
    } else if (sscanf(argv[i], "--compression_ratio=%lf%c", &d, &junk) == 1) {
      FLAGS_compression_ratio = d;
    } else if (sscanf(argv[i], "--histogram=%d%c", &n, &junk) == 1 &&
               (n == 0 || n == 1)) {
      FLAGS_histogram = n;
    } else if (sscanf(argv[i], "--use_existing_db=%d%c", &n, &junk) == 1 &&
               (n == 0 || n == 1)) {
      FLAGS_use_existing_db = n;
    } else if (sscanf(argv[i], "--num=%d%c", &n, &junk) == 1) {
      FLAGS_num = n;
    } else if (sscanf(argv[i], "--reads=%d%c", &n, &junk) == 1) {
      FLAGS_reads = n;
    } else if (sscanf(argv[i], "--value_size=%d%c", &n, &junk) == 1) {
      FLAGS_value_size = n;
    } else if (leveldb::Slice(argv[i]).starts_with("--configuration=")) {
      const char *cfg = argv[i] + strlen("--configuration=");
      if (!strcmp(cfg, "def16")) {
        FLAGS_key_size = 16;
        FLAGS_configuration = kDefault16;
      }
      else if (!strcmp(cfg, "pax16")) {
        FLAGS_key_size = 16;
        FLAGS_configuration = kPax16;
      }
      else if (!strcmp(cfg, "pax8")) {
        FLAGS_key_size = 8;
        FLAGS_configuration = kPax8;
      }
      else {
        printf("Unknown configuration - run --help for options\n");
        exit(1);
      }
    } else if (sscanf(argv[i], "--cache_size=%d%c", &n, &junk) == 1) {
      FLAGS_cache_size = n;
    } else if (strncmp(argv[i], "--db=", 5) == 0) {
      FLAGS_db = argv[i] + 5;
    } else {
      fprintf(stderr, "Invalid flag '%s'\n", argv[i]);
      exit(1);
    }
  }

  // Choose a location for the test database if none given with --db=<path>
  if (FLAGS_db == NULL) {
      leveldb::Env::Default()->GetTestDirectory(&default_db_path);
      default_db_path += "/dbbench/ham.db";
      FLAGS_db = default_db_path.c_str();
  }

  leveldb::Benchmark benchmark;
  benchmark.Run();
  return 0;
}
