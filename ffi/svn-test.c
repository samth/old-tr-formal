#include <svn_client.h>
#include <apr.h>
#include <svn_pools.h>


int main(){

  apr_pool_t * pool;

  svn_opt_revision_t rev ;
  
  svn_client_ctx_t * ctx;

  apr_initialize();

  rev.kind = svn_opt_revision_head;

  pool = svn_pool_create(NULL);

  svn_client_create_context (&ctx, pool);

  svn_auth_open (&ctx->auth_baton, apr_array_make (pool, 0, 1), pool);      

  svn_client_checkout(NULL, "http://svn.collab.net/repos/svn/trunk/ac-helpers", "foo", &rev, 1, ctx, pool);
  return 0;
}

// ROGER : 651 439 5330 rm 121

