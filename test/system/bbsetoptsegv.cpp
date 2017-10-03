#include "smt/smt_engine.h"

using namespace std;
using namespace CVC4;

int main() {
  ExprManager em;
  SmtEngine smt(&em);

  smt.setOption("bitblast", SExpr("eager"));
  smt.setOption("bitblast", SExpr("lazy"));
  
  Expr x = em.mkVar("x", em.mkBitVectorType(2));
  Expr y = em.mkVar("y", em.mkBitVectorType(2));
  Expr zx = em.mkExpr (kind::BITVECTOR_CONCAT, x, y);
  Expr zy = em.mkExpr (kind::BITVECTOR_CONCAT, y, x);
  Expr eq = em.mkExpr(kind::DISTINCT, zx, zy);
  smt.assertFormula (eq);
  Result res = smt.checkSat ();

  return 0;
}
