import Theorems.AmGm.A
import Theorems.AmGm.B

/-!
# AM–GM: statements A and B are equivalent (Euler)

Matching proof: each direction takes the other statement as hypothesis, specialises it to the
same `n`, `x`, hypotheses, and matches the two sides (B's `geomMean`/`arithMean` unfold to A's
expressions). Neither statement is proved here.
-/

namespace TuriMath.AmGm

theorem equiv : A.Statement ↔ B.Statement := by
  constructor
  · intro h n hn x hx
    have := h n hn x hx
    simpa only [B.geomMean, B.arithMean] using this
  · intro h n hn x hx
    have := h n hn x hx
    simpa only [B.geomMean, B.arithMean] using this

end TuriMath.AmGm
