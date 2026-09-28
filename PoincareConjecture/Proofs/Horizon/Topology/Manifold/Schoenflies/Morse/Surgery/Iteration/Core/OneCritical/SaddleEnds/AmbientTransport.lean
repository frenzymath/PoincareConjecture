import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.UpperFamily



noncomputable section
set_option autoImplicit false
open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
variable {v : E3} {g g' : S2 → E3} {B : Set Real}



def congrEmbedding (D : SphereSurgeryCoreCap v g B)
    (heq : EqOn g' g (D.chart '' closedBall (0 : E2) 1)) :
    SphereSurgeryCoreCap v g' B :=
  { D with
    parametrization_eq := fun x hx =>
      (heq (mem_image_of_mem D.chart hx)).trans (D.parametrization_eq x hx) }



def LowerAnnularEnd.congrEmbedding
    {D : SphereSurgeryCoreCap v g B} {C : Set S2} {h : S2 → Real} {a b : Real}
    (A : LowerAnnularEnd D C h a b)
    (heq : EqOn g' g (D.chart '' closedBall (0 : E2) 1))
    (hheight : ∀ p, inner Real v (g' p) = inner Real v (g p)) :
    LowerAnnularEnd (D.congrEmbedding heq) C h a b :=
  { A with
    actual_height := by
      intro q t ht
      rw [hheight]
      exact A.actual_height q t ht }

def UpperAnnularEnd.congrEmbedding
    {D : SphereSurgeryCoreCap v g B} {C : Set S2} {h : S2 → Real} {a b : Real}
    (A : UpperAnnularEnd D C h a b)
    (heq : EqOn g' g (D.chart '' closedBall (0 : E2) 1))
    (hheight : ∀ p, inner Real v (g' p) = inner Real v (g p)) :
    UpperAnnularEnd (D.congrEmbedding heq) C h a b where
  reflected := { A.reflected with
    actual_height := by
      intro q t ht
      have hh := A.reflected.actual_height q t ht
      change inner Real v (Poincare.Geometry.Euclidean.heightReflection D.unit_v
        (g' (A.reflected.chart (q, t)))) = t
      rw [Poincare.Geometry.Euclidean.inner_heightReflection, hheight]
      simpa only [Poincare.Geometry.Euclidean.inner_heightReflection] using hh }

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap
