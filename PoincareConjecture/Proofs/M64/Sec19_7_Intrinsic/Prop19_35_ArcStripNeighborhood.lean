import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcStripSeparation

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

theorem m64Intrinsic_exists_strip_neighborhood_width
    (F : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (hsource : ∀ t ∈ Icc (0 : ℝ) 1, (t, (0 : ℝ)) ∈ F.source)
    {O : Set AnnulusCoordinates} (hO : IsOpen O)
    (haxis : ∀ t ∈ Icc (0 : ℝ) 1, F (t, (0 : ℝ)) ∈ O) :
    ∃ delta > 0, Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta ⊆ F.source ∧
      F '' (Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta) ⊆ O := by
  let H := F.restrOpen (F.source ∩ F ⁻¹' O) (F.isOpen_inter_preimage hO)
  have hs : ∀ t ∈ Icc (0 : ℝ) 1, (t, (0 : ℝ)) ∈ H.source :=
    fun t ht => ⟨hsource t ht, hsource t ht, haxis t ht⟩
  obtain ⟨delta, hdelta, hstrip⟩ := exists_strip_source_width H hs
  refine ⟨delta, hdelta, fun q hq => (hstrip hq).1, ?_⟩
  rintro z ⟨q, hq, rfl⟩
  exact (hstrip hq).2.2

end PoincareConjecture
