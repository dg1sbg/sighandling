// ============================================================================
//  SIGNAL HANDLING TESTS
// ============================================================================
//
//  main.cpp
//  sighandling
//
//  Created by Frank Goenninger on 18.11.17.
//  Copyright © 2017 Goenninger B&T. All rights reserved.
//
// ============================================================================

// ----------------------------------------------------------------------------
// SYSTEM INCLUDES
// ----------------------------------------------------------------------------

#include <string>
#include <functional>

#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cerrno>

#include <libgen.h>
#include <string.h>
#include <unistd.h>
#include <signal.h>
#include <sys/types.h>
#include <sys/mman.h>
#include <pthread.h>
#include <execinfo.h>

namespace signal_handling
{
  // --------------------------------------------------------------------------
  // APPLICATION INCLUDES
  // --------------------------------------------------------------------------

  // --------------------------------------------------------------------------
  // MACROS
  // --------------------------------------------------------------------------

#if defined( CLASP_FALSE )
#warn "Redefining CLASP_FALSE ..."
#undef CLASP_FALSE
#endif
#define CLASP_FALSE false

#if defined( CLASP_TRUE )
#warn "Redefining CLASP_TRUE ..."
#undef CLASP_TRUE
#endif
#define CLASP_TRUE true

#define DEFINE_O_SMART_POINTERS(zclass) \
class zclass##_O; \
typedef smart_ptr<zclass##_O> zclass##_sp; /* Stack pointers */ \
typedef multiple_values<zclass##_O> zclass##_mv;

#define SMART(zclass) \
DEFINE_O_SMART_POINTERS(zclass)

#define FORWARD(zclass) \
DEFINE_O_SMART_POINTERS(zclass)

#if defined( __APPLE__ )

  // Get info from ucontext
#define STACK_SIZE     ps_ucontext->uc_stack.ss_size
#define STACK_POINTER  ps_ucontext->uc_stack.ss_sp
#define STACK_FLAGS    ps_ucontext->uc_stack.ss_flags

  // Get info from mcontext
#define RAX ps_mcontext->__ss.__rax
#define RBX ps_mcontext->__ss.__rbx
#define RCX ps_mcontext->__ss.__rcx
#define RDX ps_mcontext->__ss.__rdx
#define RDI ps_mcontext->__ss.__rdi
#define RBP ps_mcontext->__ss.__rbp
#define RSP ps_mcontext->__ss.__rsp
#define R8 ps_mcontext->__ss.__r8
#define R9 ps_mcontext->__ss.__r9
#define R10 ps_mcontext->__ss.__r10
#define R11 ps_mcontext->__ss.__r11
#define R12 ps_mcontext->__ss.__r12
#define R13 ps_mcontext->__ss.__r13
#define R14 ps_mcontext->__ss.__r14
#define R15 ps_mcontext->__ss.__r15
#define RIP ps_mcontext->__ss.__rip
#define RFLAGS ps_mcontext->__ss.__rflags
#define CS ps_mcontext->__ss.__cs

#endif

  // --------------------------------------------------------------------------
  // TYPE DEFINITIONS
  // --------------------------------------------------------------------------

  typedef int32_t rc_t;

  typedef std::function< void ( void * ) > thread_fn_t;
  typedef std::function< void ( void * ) > thread_cleanup_fn_t;
  // typedef std::function< void ( int, siginfo_t *, void * )> signal_handler_fn_t;
  typedef void (*signal_handler_fn_t)( int, siginfo_t *, void * );

  typedef uint64_t clasp_addr_t;

  // --------------------------------------------------------------------------
  // FORWARD DECLARATIONS
  // --------------------------------------------------------------------------

  static void create_pthread_key( void );
  static void signal_action( int n_signal,
                             siginfo_t * ps_siginfo,
                             void * pv_context );

  // --------------------------------------------------------------------------
  // CONSTANTS
  // --------------------------------------------------------------------------

  const rc_t   RC_OK        = EXIT_SUCCESS;
  const rc_t   RC_FAILURE   = EXIT_FAILURE;

  const size_t gn_mempagesize  = (size_t) getpagesize();
  const size_t gn_sigstacksize = SIGSTKSZ * 4;
  const size_t gn_total_mmap_size = 2 * gn_mempagesize + gn_sigstacksize;

  const int    gn_mmap_prot_rw    = PROT_READ | PROT_WRITE;
  const int    gn_mmap_prot_none  = PROT_NONE;
  const int    gn_mmap_flags      = MAP_PRIVATE | MAP_ANON;

  const int    gn_sigaction_flags = SA_RESTART | SA_SIGINFO | SA_ONSTACK | SA_NOCLDWAIT;

  // --------------------------------------------------------------------------
  // GLOBAL VARS
  // --------------------------------------------------------------------------

  // STREAM TO OUTPUT VERBOSE INFO TO
  static FILE                 * gh_default_pprint_stream = nullptr;
  static FILE                 * gh_pprint_stream = gh_default_pprint_stream;

  // SIGNAL HANDLING
  static struct sigaction       gs_prev_sigaction;
  static std::string            gs_default_sigmsg( "SIGNAL EXCEPTION" );
  static signal_handler_fn_t    gfn_signal_handler = signal_action;

  // PTHREADS
  static pthread_key_t          go_pthread_key;
  static pthread_once_t         gn_pthread_key_once = PTHREAD_ONCE_INIT;
  static int                    gn_process_term_sig = SIGTERM;

  // VERBOSITY FLAGS
  static bool                   gb_verbose_signal_info       = true;
  static bool                   gb_pprint_sysinfo_on_signal  = true;
  static bool                   gb_pprint_ucontext_on_signal = true;

  // EXE NAME
  static char                 * gpc_myself = nullptr;

  // --------------------------------------------------------------------------
  // IMPLEMENTATION
  // --------------------------------------------------------------------------

  // Mimicing Clasp's Class Hierarchy

  class GCObject {};
  class _RootDummyClass {};
  class T_O : public _RootDummyClass {};
  class General_O : public T_O {};
  class CxxObject_O : public General_O {} ;

  template <class T>
  class SmartPtr
  {

  public:

    typedef T Type;
    Type * mp_object;

    inline SmartPtr() noexcept : mp_object( nullptr ) {};
    inline SmartPtr( const SmartPtr<Type> &obj ) : mp_object( obj.mp_object ){};

    void reset( void ) { mp_object = nullptr; };
    T_O * raw( void ) const { return reinterpret_cast< T_O * >( mp_object ); };

    template < class U >
    inline bool operator==( SmartPtr<U> const other ) const
    {
      return reinterpret_cast< clasp_addr_t >( mp_object ) == reinterpret_cast< clasp_addr_t >( other.mp_object );
    }

    template <class U>
    inline bool operator!=( SmartPtr<U> const other ) const
    {
      return reinterpret_cast< clasp_addr_t >( mp_object ) != reinterpret_cast< clasp_addr_t >( other.mp_object );
    }

  };

  typedef SmartPtr<T_O> T_sp;

  // Class Implementations

  class SignalException_O : std::exception, public CxxObject_O
  {
  public:

    SignalException_O( const std::string & m = gs_default_sigmsg ) :
    m_msg( m )
    {
      memset( &m_siginfo, 0, sizeof( m_siginfo ));
      m_ucontext = nullptr;
    };
    ~SignalException_O() noexcept {};

    const char* what( void ) const noexcept { return (const char *)m_msg.c_str(); };

    void set_siginfo( siginfo_t s_siginfo ) { m_siginfo  = s_siginfo; };
    void set_ucontext( void *pv_ucontext ) { m_ucontext = pv_ucontext; };

    siginfo_t   siginfo( void ) noexcept { return m_siginfo; };
    void       *ucontext( void ) noexcept { return m_ucontext; };

  private:

    // METHODS

    // SLOTS

    std::string m_msg;
    siginfo_t   m_siginfo;
    void        *m_ucontext;
  };

  // CLASS PROCESS_O
  // This is a minimalistic wrapper class for a pthread. Demonstrates usage of
  // pthreads API calls to manage thread lifecycle and also thread local storage.

  class Process_O : public CxxObject_O
  {
  private:

    // METHODS

    void init( void )
    {
      fprintf( stderr, "%s (%s@%s:%d): INFO: Process being initialized ...\n",
              gpc_myself,
              __FUNCTION__, basename((char *)__FILE__), __LINE__ );

      // Initialize pthread thread local storage
      (void) pthread_once( &gn_pthread_key_once, create_pthread_key );

      fprintf( stderr, "%s (%s@%s:%d): INFO: Process initialization done.\n",
              gpc_myself,
              __FUNCTION__, basename((char *)__FILE__), __LINE__ );
    }

    void destroy( void )
    {
      fprintf( stderr, "%s (%s@%s:%d): INFO: Process being destroyed.\n",
              gpc_myself,
              __FUNCTION__, basename((char *)__FILE__), __LINE__ );
    }

    // SLOTS

    std::string           m_name;
    pthread_t             m_pthread;
    thread_fn_t           m_thread_fn;
    thread_cleanup_fn_t   m_thread_cleanup_fn;
    int                   m_process_term_sig;

  public:

    Process_O( thread_fn_t p_fn = nullptr,
               std::string name = "",
               thread_cleanup_fn_t p_cleanup_fn = nullptr,
               int n_process_term_sig  = gn_process_term_sig ) :
               m_thread_fn( p_fn ),
               m_name( name ),
               m_thread_cleanup_fn( p_cleanup_fn ),
               m_process_term_sig( n_process_term_sig )
    {
      init();
    };

    ~Process_O() noexcept { destroy(); };

    void send_signal( int sig ){ pthread_kill( this->m_pthread, sig ); };
    // void register_cleanup_fn( thread_cleanup_fn_t p_fn ) { };

    static std::shared_ptr<Process_O> make_process( thread_fn_t p_fn, std::string& name ) noexcept(false)
    {
      return std::make_shared<Process_O>( p_fn, name );
    }
  };

  static void create_pthread_key( void )
  {
    (void) pthread_key_create( &go_pthread_key, NULL);
  }

  // Print binary number represented as boolean array.
  // the most significant bits go first in the output
  void fprintf_bin( bool *bits, int nbits, FILE * h_stream )
  {
    if( h_stream == nullptr )
      h_stream = stderr;

    for( auto i = nbits; i-- > 0; )
    {
      fputc( "01" [ bits [ i ] ], h_stream );
      if (i % 8 == 0)
        fputc(' ', h_stream );
    }

    return;
  }

  // Convert an integer to binary representation as boolean array.
  // the least significant bit is at the start (index 0) of the array
  void ull_to_bin( uint64_t n, bool *bits, int nbits )
  {
    for( auto i = 0; i < nbits; i++ )
      bits[ i ] = ( n >> i ) & 1; //store the ith bit in b[i]
  }

  // prettyprint siginfo_t struct
  void pprint_siginfo( siginfo_t * ps_siginfo, FILE *h_stream )
  {
    if( h_stream == nullptr )
      h_stream = stderr;

    fprintf( h_stream, "\n-------------------------------------------------------------\n" );
    fprintf( h_stream, "SIGINFO:\n" );
    fprintf( h_stream, "* si_signo .... : %d\n", ps_siginfo->si_signo );
    fprintf( h_stream, "* si_code ..... : %d\n", ps_siginfo->si_code );
    fprintf( h_stream, "* si_errno .... : %d (%s)\n", ps_siginfo->si_errno, std::strerror( ps_siginfo->si_errno ) );
    fprintf( h_stream, "* si_status ... : %d\n", ps_siginfo->si_status );
    fprintf( h_stream, "* si_band ..... : %ld\n", ps_siginfo->si_band );
    fprintf( h_stream, "* si_pid ...... : %ld\n", (long int) ps_siginfo->si_pid );
    fprintf( h_stream, "* si_uid ...... : %ld\n", (long int) ps_siginfo->si_uid );
    fprintf( h_stream, "* si_addr ..... : 0x%016llx\n", ps_siginfo->si_addr );

    return;
  }

  // prettyprint ucontext_t and mcontext_t structs
  void pprint_ucontext( ucontext_t * ps_ucontext, FILE *h_stream )
  {
    const int n_bits = 8 * sizeof( uint64_t );
    bool an_bits[ n_bits ];

    if( h_stream == nullptr )
      h_stream = stderr;

    mcontext_t ps_mcontext = ps_ucontext->uc_mcontext;

    // I know, never call printf from a signal handler. But ... whatelse?

    fprintf( h_stream, "\n-------------------------------------------------------------\n" );

    fprintf( h_stream, "UCONTEXT:\n" );
    fprintf( h_stream, "* stack size .. : %lu bytes\n", STACK_SIZE );
    fprintf( h_stream, "* stack pointer : #x%016llx\n", STACK_POINTER );
    fprintf( h_stream, "* stack flags . : #x%016x\n", STACK_FLAGS );
    fprintf( h_stream, "*                 #b" );

    memset( an_bits, 0, sizeof( an_bits ));
    ull_to_bin( STACK_FLAGS, an_bits, sizeof( STACK_FLAGS ));
    fprintf_bin( an_bits, n_bits, h_stream );
    fprintf( h_stream, "\n" );

    fprintf( h_stream, "MCONTEXT:\n" );
    fprintf( h_stream, "* rax ......... : #x%016llx\n", RAX );
    fprintf( h_stream, "* rbx ......... : #x%016llx\n", RBX );
    fprintf( h_stream, "* rcx ......... : #x%016llx\n", RCX );
    fprintf( h_stream, "* rdx ......... : #x%016llx\n", RDX );
    fprintf( h_stream, "* rdi ......... : #x%016llx\n", RDI );
    fprintf( h_stream, "* rbp ......... : #x%016llx\n", RBP );
    fprintf( h_stream, "* rsp ......... : #x%016llx\n", RSP );
    fprintf( h_stream, "* r8 .......... : #x%016llx\n", R8 );
    fprintf( h_stream, "* r9 .......... : #x%016llx\n", R9 );
    fprintf( h_stream, "* r10 ......... : #x%016llx\n", R10 );
    fprintf( h_stream, "* r11 ......... : #x%016llx\n", R11 );
    fprintf( h_stream, "* r12 ......... : #x%016llx\n", R12 );
    fprintf( h_stream, "* r13 ......... : #x%016llx\n", R13 );
    fprintf( h_stream, "* r14 ......... : #x%016llx\n", R14 );
    fprintf( h_stream, "* r15 ......... : #x%016llx\n", R15 );
    fprintf( h_stream, "* rip ......... : #x%016llx\n", RIP );
    fprintf( h_stream, "* value at rip  : #x%016x\n", * (uint32_t *) RIP );
    fprintf( h_stream, "* rflags ...... : #x%016llx\n", RFLAGS );
    fprintf( h_stream, "*                 #b" );

    memset( an_bits, 0, sizeof( an_bits ));
    ull_to_bin( RFLAGS, an_bits, n_bits);
    fprintf_bin( an_bits, n_bits, h_stream );
    fprintf( h_stream, "\n" );

    fprintf( h_stream, "* cs .......... : 0x%016llx\n", CS );

    return;
  }

  static void unblock_signal( int n_sig )
  {
    sigset_t n_sigs;

    sigemptyset( &n_sigs );
    sigaddset( &n_sigs, n_sig );
    sigprocmask( SIG_UNBLOCK, &n_sigs, NULL );
  }

  void register_signal( int n_sig, struct sigaction *ps_sigaction )
  {
    unblock_signal( n_sig );
    sigaction( n_sig, ps_sigaction, nullptr );
  }

  // Default signal action
  static void signal_action( int n_signal,
                             siginfo_t * ps_siginfo,
                             void *pv_context )
  {
    SignalException_O e;

    if( gb_verbose_signal_info == true )
    {
      fprintf( stderr, "\n%s: In SIGNAL_ACTION.\n", gpc_myself );
      fprintf( stderr, "%s: Received signal %d.\n", gpc_myself, n_signal );
    }

    if( n_signal == SIGABRT )
    {
      if( gb_verbose_signal_info == true )
      {
        fprintf( stderr, "%s: Exiting - signal %d makes process terminate.\n", gpc_myself, n_signal );
      }

      _exit( -n_signal );
    }

    if( gb_pprint_sysinfo_on_signal == true )
    {
      pprint_siginfo( ps_siginfo, gh_pprint_stream );
    }

    if( gb_pprint_ucontext_on_signal == true )
    {
      pprint_ucontext( reinterpret_cast<ucontext_t *>( pv_context ), gh_pprint_stream );
    }

    e.set_siginfo( * ps_siginfo );
    e.set_ucontext( pv_context );

    if( gb_verbose_signal_info == true )
    {
      fprintf( stderr, "%s: Throwing exception \"%s\".\n", gpc_myself, e.what() );
    }

    throw e;
  }

  rc_t init_signal_handling( signal_handler_fn_t fn_signal_handler )
  {
    rc_t n_rc = RC_OK;

    char     * pc_mem         = nullptr;
    char     * pc_stack_addr  = nullptr;
    char     * pc_page_1_addr = nullptr;
    char     * pc_page_2_addr = nullptr;

    stack_t           s_sigstk;
    struct sigaction  s_sigaction;

    memset( &s_sigstk, 0, sizeof( s_sigstk ) );
    memset( &s_sigaction, 0, sizeof( s_sigaction ) );
    memset( &gs_prev_sigaction, 0, sizeof( s_sigaction ) );

    // Allocate memory for safe signal handling

    pc_mem = (char *) mmap ( nullptr,
                            gn_total_mmap_size,
                            gn_mmap_prot_rw,
                            gn_mmap_flags,
                            -1,
                            0 );

    if ( pc_mem != MAP_FAILED )
    {
      // Set addresses of memory regions

      pc_page_1_addr = pc_mem;
      pc_stack_addr  = pc_mem + gn_mempagesize;
      pc_page_2_addr = pc_stack_addr + gn_sigstacksize;

      // Protect signal stack against unintented memory writes

      n_rc = mprotect( pc_page_1_addr, gn_mempagesize, gn_mmap_prot_none );
      if( n_rc != RC_OK )
      {
        fprintf( stderr, "%s: *** Could not protect memory page 1\n", gpc_myself );
        _exit( EXIT_FAILURE );
      }

      n_rc = mprotect( pc_page_2_addr, gn_mempagesize, gn_mmap_prot_none );
      if( n_rc != RC_OK )
      {
        fprintf( stderr, "%s: *** Could not protect memory page 2\n", gpc_myself );
        _exit( EXIT_FAILURE );
      }

      // Setup signal stack

      s_sigstk.ss_sp   = pc_stack_addr;
      s_sigstk.ss_size = gn_sigstacksize;

      if ( sigaltstack ( &s_sigstk, 0 ) < 0 )
      {
        s_sigstk.ss_size = 0;
        fprintf ( stderr, "%s: *** sigaltstack errno = %d\n", gpc_myself, errno );
        n_rc = RC_FAILURE;
      }
      else
      {
        // Now setup the signal handler

        s_sigaction.sa_flags = gn_sigaction_flags;

        sigemptyset( &s_sigaction.sa_mask );

        if( fn_signal_handler == nullptr )
        {
          fn_signal_handler = gfn_signal_handler;
        }

        if( fn_signal_handler != nullptr )
        {
          // auto pf_target = fn_signal_handler.target< void( int, __siginfo *, void * ) >();
          // auto pf_target = fn_signal_handler;
          // fprintf( stderr, "%s (%s@%s:%d): DEBUG: pf_target = 0x%016llx\n",
          //          gpc_myself,
          //          __FUNCTION__, basename((char *)__FILE__), __LINE__,
          //          pf_target );

          s_sigaction.sa_sigaction = fn_signal_handler;// This is the handling fn
        }
        else
        {
          fprintf( stderr, "WARNING: %s(%s:%d): Signal handler function is nullptr!", __FUNCTION__, basename((char *)__FILE__), __LINE__);
        }

        // Signals SIGKILL and SIGSTOP are handled by the kernel and cannot be
        // caught. SIGTRAP is needed by debuggers and shouldn't be handled by user.
        register_signal( SIGQUIT,   &s_sigaction );
        register_signal( SIGHUP,    &s_sigaction );
        register_signal( SIGINT,    &s_sigaction );
        register_signal( SIGILL,    &s_sigaction );
        register_signal( SIGABRT,   &s_sigaction );
        register_signal( SIGFPE,    &s_sigaction );
        register_signal( SIGKILL,   &s_sigaction ); // actually won't work
        register_signal( SIGSEGV,   &s_sigaction );
        register_signal( SIGPIPE,   &s_sigaction );
        register_signal( SIGALRM,   &s_sigaction );
        register_signal( SIGTERM,   &s_sigaction );
        register_signal( SIGUSR1,   &s_sigaction );
        register_signal( SIGUSR2,   &s_sigaction );
        register_signal( SIGCHLD,   &s_sigaction );
        register_signal( SIGCONT,   &s_sigaction );
        register_signal( SIGSTOP,   &s_sigaction ); // actually won't work
        register_signal( SIGTSTP,   &s_sigaction );
        register_signal( SIGTTIN,   &s_sigaction );
        register_signal( SIGTTOU,   &s_sigaction );
        register_signal( SIGBUS,    &s_sigaction );
        register_signal( SIGIO,     &s_sigaction );
        register_signal( SIGPROF,   &s_sigaction );
        register_signal( SIGSYS ,   &s_sigaction );
        // register_signal( SIGTRAP,   &s_sigaction );
        register_signal( SIGURG,    &s_sigaction );
        register_signal( SIGVTALRM, &s_sigaction );
        register_signal( SIGXCPU,   &s_sigaction );
        register_signal( SIGXFSZ,   &s_sigaction );
        register_signal( SIGIOT,    &s_sigaction );
        register_signal( SIGEMT,    &s_sigaction );
#if !defined( __APPLE__ )
        register_signal( SIGSTKFLT, &s_sigaction ); // Not available in macOS!
        register_signal( SIGPWR, &s_sigaction );    // Not available in macOS!
#endif
        register_signal( SIGWINCH,  &s_sigaction );
      }
    }
    else
    {
      fprintf ( stderr, "%s(%s:%d): malloc (SIGSTKSZ) failed!\n",  __FUNCTION__, basename((char *)__FILE__), __LINE__);
      n_rc = RC_FAILURE;
    }
    return n_rc;
  };

} // namespace

// ----------------------------------------------------------------------------
// M A I N
// ----------------------------------------------------------------------------

// USING NAMESPACES FOR SIMPLICITY

using namespace signal_handling;
using namespace std;

//   M A I N   F U N C T I O N

int main( int n_argc, char **ppc_argv )
{
  rc_t n_rc = RC_OK;

  // Setup MYSELF for verbose error msgs

  gpc_myself = strdup( basename( ppc_argv[ 0 ] ) );

  fprintf( stderr, "%s (%s@%s:%d): INFO: Pid = %d.\n",
          gpc_myself,
          __FUNCTION__, basename((char *)__FILE__), __LINE__,
          getpid() );

  // Intitialize signal handling

  n_rc = init_signal_handling( nullptr );
  if( n_rc == RC_OK )
  {
    fprintf( stderr, "%s (%s@%s:%d): INFO: Signal handling successfully initialized.\n",
            gpc_myself,
            __FUNCTION__, basename((char *)__FILE__), __LINE__ );
  }
  else
  {
    fprintf( stderr, "%s (%s@%s:%d): CRITICAL: Signal handling initialization error %d!\n",
             gpc_myself,
             __FUNCTION__, basename((char *)__FILE__), __LINE__,
             n_rc );
  }

  // fprintf( stderr, "%s (%s@%s:%d): DEBUG: signal_handler @ 0x%016llx\n",
  //        gpc_myself,
  //        __FUNCTION__, basename((char *)__FILE__), __LINE__,
  //        signal_action );

  // SLEEP - WTHIN THIS TIME USER MAY SEND SIGNAL EXTERNALLY TO TEST REACTION
  // This try/catch/throw pattern garantuees stack unwinding.

  try // - This is at the top-most level of the control domain
  {
    sleep( 15 );  // the business function - whatever ...
  }
  catch ( exception& e ) // Here, stack is not yet unwound
  {
    fprintf( stderr, "%s (%s@%s:%d): EXCEPTION: %s.\n",
            gpc_myself,
            __FUNCTION__, basename((char *)__FILE__), __LINE__,
            e.what() );

    throw;
    // Now stack is unwound.
  }

  // EXIT

  fprintf( stderr, "%s (%s@%s:%d): INFO: Exiting.\n",
          gpc_myself,
          __FUNCTION__, basename((char *)__FILE__), __LINE__ );

  free( gpc_myself );
  return (int) n_rc;
}
