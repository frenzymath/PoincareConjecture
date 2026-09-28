import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.TerminalData



noncomputable section
set_option autoImplicit false
open Set Metric Function
open scoped Manifold ContDiff Topology
namespace Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview
private abbrev E3 := EuclideanSpace Real (Fin 3)

def Rz : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ where
  toFun y := WithLp.toLp 2 ![y 0, y 1, -y 2]
  invFun y := WithLp.toLp 2 ![y 0, y 1, -y 2]
  left_inv y := by ext i; fin_cases i <;> simp
  right_inv y := by ext i; fin_cases i <;> simp
  contMDiff_toFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).contDiff.neg
  contMDiff_invFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).contDiff.neg

@[simp] theorem Rz_zero (y : E3) : Rz y 0 = y 0 := rfl
@[simp] theorem Rz_one (y : E3) : Rz y 1 = y 1 := rfl
@[simp] theorem Rz_two (y : E3) : Rz y 2 = -y 2 := rfl
@[simp] theorem Rz_involutive (y : E3) : Rz (Rz y) = y := Rz.symm_apply_apply y

theorem Rz_height (y : E3) : (Rz y) 2 = -y 2 := by simp



theorem reflected_transport_height
    (T S : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (q : E3) (c s : Real)
    (hT : ∀ y, (T y) 2 = -c + s * (y 2 - (S q) 2)) :
    ∀ y, (((Rz.trans T).trans Rz) y) 2 =
      c + s * (y 2 - ((S.trans Rz) q) 2) := by
  intro y
  change (Rz (T (Rz y))) 2 = c + s * (y 2 - (Rz (S q)) 2)
  rw [Rz_height, hT, Rz_two, Rz_two]
  ring

theorem reflected_matching_conjugation
    (T S : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (x : E3) :
    ((Rz.trans T).trans Rz) ((S.trans Rz) x) = Rz (T (S x)) := by
  change Rz (T (Rz (Rz (S x)))) = _
  rw [Rz_involutive]

end Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview
