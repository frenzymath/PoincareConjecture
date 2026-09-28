import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Models
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.SphereCharts

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_antipodal_ball_neighborhood
    (b : OpenPartialHomeomorph E3 UnitThreeSphere)
    (hs : closedBall 0 1 ⊆ b.source)
    (hdis : Disjoint (b '' closedBall 0 1) (Neg.neg '' (b '' closedBall 0 1))) :
    ∃ R : ℝ, 1 < R ∧ closedBall 0 R ⊆ b.source ∧
      Disjoint (b '' closedBall 0 R) (Neg.neg '' (b '' closedBall 0 R)) := by
  let K := b '' closedBall 0 1
  have hK : IsCompact K := (isCompact_closedBall 0 1).image_of_continuousOn
    (b.continuousOn.mono hs)
  have hnegK : IsCompact (Neg.neg '' K) := hK.image continuous_neg
  obtain ⟨U, V, hU, hV, hKU, hKV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact hK hnegK hdis
  let W := U ∩ Neg.neg ⁻¹' V
  have hW : IsOpen W := hU.inter (hV.preimage continuous_neg)
  have hKW : K ⊆ W := fun x hx => ⟨hKU hx, hKV (mem_image_of_mem Neg.neg hx)⟩
  have hWdis : Disjoint W (Neg.neg '' W) := by
    apply disjoint_left.mpr
    rintro x hx ⟨y, hy, rfl⟩
    exact disjoint_left.mp hUV hx.1 hy.2
  have hpre : IsOpen (b.source ∩ b ⁻¹' W) :=
    b.continuousOn.isOpen_inter_preimage b.open_source hW
  have hsmall : closedBall (0 : E3) 1 ⊆ b.source ∩ b ⁻¹' W :=
    fun x hx => ⟨hs hx, hKW (mem_image_of_mem b hx)⟩
  obtain ⟨δ, hδ, henlarge⟩ := (isCompact_closedBall (0 : E3) 1).exists_cthickening_subset_open
    hpre hsmall
  rw [cthickening_closedBall hδ.le zero_le_one] at henlarge
  refine ⟨δ + 1, by linarith, henlarge.trans inter_subset_left, ?_⟩
  have himage : b '' closedBall 0 (δ + 1) ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact (henlarge hx).2
  exact hWdis.mono himage (image_mono himage)

theorem exists_exponential_antipodal_ball_neighborhood
    (b : OpenPartialHomeomorph E3 UnitThreeSphere)
    (hs : closedBall 0 1 ⊆ b.source)
    (hdis : Disjoint (b '' closedBall 0 1) (Neg.neg '' (b '' closedBall 0 1))) :
    ∃ δ : ℝ, 0 < δ ∧ closedBall 0 (Real.exp (2 * δ)) ⊆ b.source ∧
      Disjoint (b '' closedBall 0 (Real.exp (2 * δ)))
        (Neg.neg '' (b '' closedBall 0 (Real.exp (2 * δ)))) := by
  obtain ⟨R, hR, hsR, hdisR⟩ := exists_antipodal_ball_neighborhood b hs hdis
  let δ := Real.log R / 2
  have hδ : 0 < δ := half_pos (Real.log_pos hR)
  have heq : Real.exp (2 * δ) = R := by
    rw [show 2 * δ = Real.log R by dsimp [δ]; ring]
    exact Real.exp_log (zero_lt_one.trans hR)
  exact ⟨δ, hδ, heq.symm ▸ hsR, heq.symm ▸ hdisR⟩

end PoincareConjecture.SphereCharts
