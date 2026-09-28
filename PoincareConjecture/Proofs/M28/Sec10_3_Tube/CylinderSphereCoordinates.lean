import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderSphereTransport
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderEndRegions











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.OpenCylinderModel

open M28

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  {U : TopologicalSpace.Opens M}

private theorem homeomorph_symm_height (T : OpenCylinderModel (U : Set M)) (x : U) :
    ((T.homeomorph.symm x).2 : ℝ) = (T.inverse x).2 := by
  have hcoord : T.coordinate
      ((T.homeomorph.symm x).1, ((T.homeomorph.symm x).2 : ℝ)) = x := by
    rw [← T.coordinate_eq]
    exact congrArg Subtype.val (T.homeomorph.apply_symm_apply x)
  have h := T.left_inverse
    (show ((T.homeomorph.symm x).1, ((T.homeomorph.symm x).2 : ℝ)) ∈
      univ ×ˢ Ioo (0 : ℝ) 1 from ⟨mem_univ _, (T.homeomorph.symm x).2.property⟩)
  rw [hcoord] at h
  exact (congrArg Prod.snd h).symm




theorem exists_isotopic_sphere_coordinates
    (T : OpenCylinderModel (U : Set M)) {S : Set M}
    (hS : SmoothSphereIsotopicIn (U : Set M) S T.middleSphere) :
    ∃ (φ : U ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1)) (a b : ℝ),
      0 < a ∧ a < 1 / 2 ∧ 1 / 2 < b ∧ b < 1 ∧
      (∀ x : U, ((φ x).2 : ℝ) = 1 / 2 ↔ (x : M) ∈ S) ∧
      ∀ x : U, (T.inverse x).2 < a ∨ b < (T.inverse x).2 →
        ((φ x).2 : ℝ) = (T.inverse x).2 := by
  obtain ⟨H, hH, hslice, hzero, hone⟩ := exists_global_smooth_sphere_isotopy hS
  obtain ⟨Ksupport, e, hK, hKA, _he, _hes, htransport, hfix⟩ :=
    exists_compact_annulus_sphere_transport T hH hslice
  have hpres (v : E₃) : v ∈ cylinderAnnulus ↔ e v ∈ cylinderAnnulus := by
    constructor
    · intro hv
      by_contra hnot
      have hvK : e v ∉ Ksupport := fun h => hnot (hKA h)
      have heq : e v = v := e.injective (hfix (e v) hvK)
      exact hnot (heq.symm ▸ hv)
    · intro hev
      by_contra hv
      exact hv ((hfix v (fun hk => hv (hKA hk))) ▸ hev)
  let eA : cylinderAnnulus ≃ₜ cylinderAnnulus := e.subtype hpres
  let φ : U ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1) :=
    ((T.annulusHomeomorph.trans eA).trans T.annulusHomeomorph.symm).trans
      T.homeomorph.symm
  have hφread (x : U) :
      ((φ x).2 : ℝ) = ‖e (T.annulusCoordinates x)‖ - 1 := by
    change ((T.homeomorph.symm
      (T.annulusHomeomorph.symm (eA (T.annulusHomeomorph x)))).2 : ℝ) = _
    rw [homeomorph_symm_height]
    change (T.inverse (T.coordinate
      (cylinderAnnulusInverse (eA (T.annulusHomeomorph x))))).2 = _
    rw [T.left_inverse ⟨mem_univ _, cylinderAnnulusInverse_mem _⟩]
    rfl
  let A : M → E₃ := fun x => cylinderRadial (T.inverse x)
  let B : E₃ → M := T.annulusAmbientInverse
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
  have hsphere (x : U) : ((φ x).2 : ℝ) = 1 / 2 ↔ (x : M) ∈ S := by
    constructor
    · intro hx
      let y : E₃ := e (A x)
      have hyA : y ∈ cylinderAnnulus :=
        (hpres (A x)).mp (T.annulusCoordinates_mem x)
      have hymiddle : B y ∈ T.middleSphere := by
        refine ⟨cylinderAnnulusInverse ⟨y, hyA⟩, ⟨mem_univ _, ?_⟩, ?_⟩
        · change ‖y‖ - 1 = 1 / 2
          exact (hφread x).symm.trans hx
        · exact (T.annulusAmbientInverse_apply ⟨y, hyA⟩).symm
      obtain ⟨q, hq⟩ := hone.symm ▸ hymiddle
      change H (1, q) = B y at hq
      have hqU : H (0, q) ∈ U := (hslice 0).2 (mem_range_self q)
      have hAy : A (H (1, q)) = y := by rw [hq]; exact hAB y hyA
      have hpre : A (H (0, q)) = A x := e.injective ((htransport q).trans hAy)
      have hpoint : H (0, q) = x := by
        calc
          H (0, q) = B (A (H (0, q))) := (hBA _ hqU).symm
          _ = B (A x) := congrArg B hpre
          _ = x := hBA _ x.property
      rw [← hpoint, ← hzero]
      exact mem_range_self q
    · intro hx
      obtain ⟨q, hq⟩ := hzero.symm ▸ hx
      change H (0, q) = (x : M) at hq
      have hqU : H (1, q) ∈ U := (hslice 1).2 (mem_range_self q)
      have hmiddle : H (1, q) ∈ T.middleSphere := hone ▸ mem_range_self q
      have hh := (T.mem_middleSphere_iff hqU).mp hmiddle
      rw [hφread]
      change ‖e (cylinderRadial (T.inverse (x : M)))‖ - 1 = 1 / 2
      rw [← hq, htransport, cylinderRadial_norm (T.inverse_mem _ hqU).2.1]
      linarith
  have hKB : IsCompact (B '' Ksupport) := hK.image_of_continuousOn
    (T.contMDiffOn_annulusAmbientInverse.continuousOn.mono hKA)
  have hKBU : B '' Ksupport ⊆ U := by
    rintro x ⟨v, hv, rfl⟩
    exact hBU v (hKA hv)
  obtain ⟨a₀, b₀, ha₀, _hab₀, hb₀, hcapture⟩ :=
    T.exists_compactSlab_capturing hKB hKBU
  refine ⟨φ, min a₀ (1 / 4), max b₀ (3 / 4),
    lt_min ha₀ (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num),
    (by norm_num : (1 / 2 : ℝ) < 3 / 4).trans_le (le_max_right _ _),
    max_lt hb₀ (by norm_num), hsphere, ?_⟩
  intro x hx
  have hxK : A x ∉ Ksupport := by
    intro hmem
    have hslab := (T.mem_compactSlab_iff ha₀ hb₀).mp
      (hcapture ⟨A x, hmem, hBA x x.property⟩)
    rcases hx with hx | hx
    · exact (not_lt_of_ge hslab.2.1) (hx.trans_le (min_le_left _ _))
    · exact (not_lt_of_ge hslab.2.2) ((le_max_left _ _).trans_lt hx)
  rw [hφread]
  change ‖e (A x)‖ - 1 = _
  rw [hfix _ hxK]
  change ‖cylinderRadial (T.inverse x)‖ - 1 = _
  rw [cylinderRadial_norm (T.inverse_mem x x.property).2.1]
  ring

end PoincareConjecture.OpenCylinderModel
