import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderSphereTransport











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.OpenCylinderModel

open M28

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  {U : TopologicalSpace.Opens M}




theorem exists_isotopic_sphere_end_crossing
    (T : OpenCylinderModel (U : Set M)) {S : Set M}
    (hS : SmoothSphereIsotopicIn (U : Set M) S T.middleSphere) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧
      ∀ γ : ℝ → M, ContinuousOn γ (Icc (0 : ℝ) 1) →
        MapsTo γ (Icc (0 : ℝ) 1) U →
        (T.inverse (γ 0)).2 < a → b < (T.inverse (γ 1)).2 →
        ∃ t ∈ Icc (0 : ℝ) 1, γ t ∈ S := by
  obtain ⟨H, hH, hslice, hzero, hone⟩ := exists_global_smooth_sphere_isotopy hS
  obtain ⟨Ksupport, e, hK, hKA, _he, _hes, htransport, hfix⟩ :=
    exists_compact_annulus_sphere_transport T hH hslice
  let A : M → E₃ := fun x => cylinderRadial (T.inverse x)
  let B : E₃ → M := T.annulusAmbientInverse
  have hAU (x : M) (hx : x ∈ U) : A x ∈ cylinderAnnulus :=
    cylinderRadial_mem (T.inverse_mem x hx).2
  have hBA (x : M) (hx : x ∈ U) : B (A x) = x := by
    let xU : U := ⟨x, hx⟩
    change T.annulusAmbientInverse (T.annulusCoordinates xU) = (xU : M)
    rw [T.annulusAmbientInverse_apply
      ⟨T.annulusCoordinates xU, T.annulusCoordinates_mem xU⟩]
    exact T.annulusParametrization_coordinates xU
  have hBU (v : E₃) (hv : v ∈ cylinderAnnulus) : B v ∈ U := by
    change T.annulusAmbientInverse v ∈ U
    rw [T.annulusAmbientInverse_apply ⟨v, hv⟩]
    exact T.annulusParametrization_mem _
  have hAB (v : E₃) (hv : v ∈ cylinderAnnulus) : A (B v) = v := by
    change A (T.annulusAmbientInverse v) = v
    rw [T.annulusAmbientInverse_apply ⟨v, hv⟩]
    exact T.annulusCoordinates_parametrization ⟨v, hv⟩
  have hpres (v : E₃) (hv : v ∈ cylinderAnnulus) : e v ∈ cylinderAnnulus := by
    by_contra hnot
    have hvK : e v ∉ Ksupport := fun h => hnot (hKA h)
    have heq : e v = v := e.injective (hfix (e v) hvK)
    exact hnot (heq.symm ▸ hv)
  have hBcont : ContinuousOn B (cylinderAnnulus : Set E₃) :=
    T.contMDiffOn_annulusAmbientInverse.continuousOn
  have hKB : IsCompact (B '' Ksupport) :=
    hK.image_of_continuousOn (hBcont.mono hKA)
  have hKBU : B '' Ksupport ⊆ U := by
    rintro x ⟨v, hv, rfl⟩
    exact hBU v (hKA hv)
  obtain ⟨a₀, b₀, ha₀, _hab₀, hb₀, hcapture⟩ :=
    T.exists_compactSlab_capturing hKB hKBU
  have htail (x : M) (hx : x ∈ U)
      (hh : (T.inverse x).2 < a₀ ∨ b₀ < (T.inverse x).2) : A x ∉ Ksupport := by
    intro hxK
    have hslab := (T.mem_compactSlab_iff ha₀ hb₀).mp
      (hcapture ⟨A x, hxK, hBA x hx⟩)
    rcases hh with hh | hh
    · exact (not_lt_of_ge hslab.2.1) hh
    · exact (not_lt_of_ge hslab.2.2) hh
  have ha : 0 < min a₀ (1 / 4 : ℝ) := lt_min ha₀ (by norm_num)
  have hb : max b₀ (3 / 4 : ℝ) < 1 := max_lt hb₀ (by norm_num)
  have hab : min a₀ (1 / 4 : ℝ) < max b₀ (3 / 4 : ℝ) :=
    (min_le_right _ _).trans_lt
      ((by norm_num : (1 / 4 : ℝ) < 3 / 4).trans_le (le_max_right _ _))
  refine ⟨min a₀ (1 / 4), max b₀ (3 / 4), ha, hab, hb, ?_⟩
  intro γ hγ hγU hlow hhigh
  have hγ₀ : γ 0 ∈ U := hγU ⟨le_rfl, zero_le_one⟩
  have hγ₁ : γ 1 ∈ U := hγU ⟨zero_le_one, le_rfl⟩
  have hfix₀ : e (A (γ 0)) = A (γ 0) :=
    hfix _ (htail _ hγ₀ (Or.inl (hlow.trans_le (min_le_left _ _))))
  have hfix₁ : e (A (γ 1)) = A (γ 1) :=
    hfix _ (htail _ hγ₁ (Or.inr ((le_max_left _ _).trans_lt hhigh)))
  have hAcont : ContinuousOn A (U : Set M) :=
    contMDiff_cylinderRadial.continuous.comp_continuousOn T.inverse_smooth.continuousOn
  have hheight : ContinuousOn (fun t => ‖e (A (γ t))‖ - 1) (Icc (0 : ℝ) 1) :=
    ((e.continuous.comp_continuousOn (hAcont.comp hγ hγU)).norm).sub continuousOn_const
  have hheight₀ : ‖e (A (γ 0))‖ - 1 = (T.inverse (γ 0)).2 := by
    rw [hfix₀]
    change ‖cylinderRadial (T.inverse (γ 0))‖ - 1 = _
    rw [cylinderRadial_norm (T.inverse_mem _ hγ₀).2.1]
    ring
  have hheight₁ : ‖e (A (γ 1))‖ - 1 = (T.inverse (γ 1)).2 := by
    rw [hfix₁]
    change ‖cylinderRadial (T.inverse (γ 1))‖ - 1 = _
    rw [cylinderRadial_norm (T.inverse_mem _ hγ₁).2.1]
    ring
  have hhalf : (1 / 2 : ℝ) ∈ Icc (‖e (A (γ 0))‖ - 1) (‖e (A (γ 1))‖ - 1) := by
    rw [hheight₀, hheight₁]
    constructor
    · have hh := hlow.trans_le (min_le_right a₀ (1 / 4 : ℝ))
      linarith
    · have hh := (le_max_right b₀ (3 / 4 : ℝ)).trans_lt hhigh
      linarith
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc zero_le_one hheight hhalf
  let y : E₃ := e (A (γ t))
  have hyA : y ∈ cylinderAnnulus := hpres _ (hAU _ (hγU ht))
  have hymiddle : B y ∈ T.middleSphere := by
    refine ⟨cylinderAnnulusInverse ⟨y, hyA⟩, ⟨mem_univ _, ?_⟩, ?_⟩
    · change ‖y‖ - 1 = 1 / 2
      exact heq
    · exact (T.annulusAmbientInverse_apply ⟨y, hyA⟩).symm
  obtain ⟨q, hq⟩ := hone.symm ▸ hymiddle
  change H (1, q) = B y at hq
  have hqU : H (0, q) ∈ U := (hslice 0).2 (mem_range_self q)
  have hAy : A (H (1, q)) = y := by
    rw [hq]
    exact hAB y hyA
  have hpre : A (H (0, q)) = A (γ t) := by
    apply e.injective
    exact (htransport q).trans hAy
  have hpoint : H (0, q) = γ t := by
    calc
      H (0, q) = B (A (H (0, q))) := (hBA _ hqU).symm
      _ = B (A (γ t)) := congrArg B hpre
      _ = γ t := hBA _ (hγU ht)
  refine ⟨t, ht, ?_⟩
  rw [← hpoint, ← hzero]
  exact mem_range_self q

end PoincareConjecture.OpenCylinderModel
