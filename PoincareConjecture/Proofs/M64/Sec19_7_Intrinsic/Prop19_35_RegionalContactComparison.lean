import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_ContactTime











set_option autoImplicit false

open Set

namespace PoincareConjecture




theorem m64Intrinsic_open_region_strictly_inside_annulus
    {U : Set AnnulusCoordinates} (hU : IsOpen U)
    (hsub : closure U ⊆ standardAnnulusDomain) :
    ∀ x ∈ U, 1 < ‖x‖ ∧ ‖x‖ < 2 := by
  have hannulus : standardAnnulusDomain =
      (Metric.ball (0 : AnnulusCoordinates) 1)ᶜ ∩
        Metric.closedBall (0 : AnnulusCoordinates) 2 := by
    ext x
    simp only [standardAnnulusDomain, mem_ofPred_eq, mem_inter_iff, mem_compl_iff,
      Metric.mem_ball, Metric.mem_closedBall, dist_zero_right]
    constructor
    · intro hx
      exact ⟨not_lt_of_ge hx.1, hx.2⟩
    · intro hx
      exact ⟨le_of_not_gt hx.1, hx.2⟩
  have hUinterior : U ⊆ interior standardAnnulusDomain :=
    interior_maximal (fun _ hx => hsub (subset_closure hx)) hU
  intro x hx
  have hxinterior := hUinterior hx
  rw [hannulus, interior_inter, interior_compl,
    closure_ball (0 : AnnulusCoordinates) (by norm_num : (1 : ℝ) ≠ 0),
    interior_closedBall (0 : AnnulusCoordinates) (by norm_num : (2 : ℝ) ≠ 0)] at hxinterior
  simpa only [mem_inter_iff, mem_compl_iff, Metric.mem_closedBall, Metric.mem_ball,
    dist_zero_right, not_le] using hxinterior




theorem m64Intrinsic_regional_contact_le_annulus_contact
    {U : Set AnnulusCoordinates} (hU : IsOpen U)
    (hsub : closure U ⊆ standardAnnulusDomain)
    {q : ℝ → AnnulusCoordinates} {R b d : ℝ} (hbR : b ≤ R) (hd : 0 < d)
    (hbefore : ∀ t ∈ Ioo (0 : ℝ) b, q t ∈ U)
    (hcontact : d = R ∨ ‖q d‖ = 1 ∨ ‖q d‖ = 2) : b ≤ d := by
  by_contra hbd
  have hdb : d < b := lt_of_not_ge hbd
  have hdinside :=
    m64Intrinsic_open_region_strictly_inside_annulus hU hsub (q d) (hbefore d ⟨hd, hdb⟩)
  rcases hcontact with hcap | hinner | houter
  · exact (not_lt_of_ge hbR) (hcap ▸ hdb)
  · linarith [hdinside.1]
  · linarith [hdinside.2]

end PoincareConjecture
