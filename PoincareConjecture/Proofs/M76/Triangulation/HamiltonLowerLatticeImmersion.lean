import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerPeriodLattice
import Mathlib.Topology.Algebra.Module.Equiv

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

def hamiltonLowerLatticePuncture (κ : Type*) :
    (κ → ℝ) ⧸ (hamiltonLowerPeriodLattice κ).toAddSubgroup :=
  QuotientAddGroup.mk (fun _ => (256 : ℝ))

structure HamiltonLowerLatticeImmersion (κ : Type*) [Fintype κ] where
  map : ((κ → ℝ) ⧸ (hamiltonLowerPeriodLattice κ).toAddSubgroup) → (κ → ℝ)
  compactCarrier : Set (κ → ℝ)
  compact : IsCompact compactCarrier
  localHomeomorph : IsLocalHomeomorphOn map {hamiltonLowerLatticePuncture κ}ᶜ
  image_subset : map '' {hamiltonLowerLatticePuncture κ}ᶜ ⊆ compactCarrier
  core : ∀ x : κ → ℝ, ‖x‖ ≤ 3 →
    QuotientAddGroup.mk x ≠ hamiltonLowerLatticePuncture κ ∧ map (QuotientAddGroup.mk x) = x
  quotientPL : LocallyPiecewiseAffineOn
    (map ∘ (QuotientAddGroup.mk : (κ → ℝ) → _))
    (QuotientAddGroup.mk ⁻¹' {hamiltonLowerLatticePuncture κ}ᶜ)

private theorem lower_immersion_of_model
    {κ V T : Type*} [Fintype κ] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace T]
    (t : ((κ → ℝ) ⧸ (hamiltonLowerPeriodLattice κ).toAddSubgroup) ≃ₜ T)
    (a : (κ → ℝ) ≃L[ℝ] V) (q : V → T) (p : T)
    (hquot : ∀ x, t (QuotientAddGroup.mk x) = q (a x))
    (hp : t (hamiltonLowerLatticePuncture κ) = p)
    (f : T → V) (K : Set V) (hK : IsCompact K)
    (hf : IsLocalHomeomorphOn f {p}ᶜ) (himage : f '' {p}ᶜ ⊆ K)
    (hcore : ∀ x : κ → ℝ, ‖x‖ ≤ 3 → q (a x) ≠ p ∧ f (q (a x)) = a x)
    (hPL : LocallyPiecewiseAffineOn (f ∘ q) (q ⁻¹' {p}ᶜ)) :
    Nonempty (HamiltonLowerLatticeImmersion κ) := by
  have hpre (x) : t x ∈ ({p}ᶜ : Set T) ↔
      x ∈ ({hamiltonLowerLatticePuncture κ}ᶜ : Set _) := by
    simp only [mem_compl_iff, mem_singleton_iff, ← hp, t.injective.eq_iff]
  have hloc : IsLocalHomeomorphOn (a.symm ∘ f ∘ t)
      {hamiltonLowerLatticePuncture κ}ᶜ :=
    a.symm.toHomeomorph.isLocalHomeomorph.isLocalHomeomorphOn.comp
      (hf.comp t.isLocalHomeomorph.isLocalHomeomorphOn (fun x hx => (hpre x).mpr hx))
      (fun _ _ => mem_univ _)
  have hdomain : a ⁻¹' (q ⁻¹' {p}ᶜ) =
      (QuotientAddGroup.mk : (κ → ℝ) → _) ⁻¹' {hamiltonLowerLatticePuncture κ}ᶜ := by
    ext x
    change q (a x) ∈ ({p}ᶜ : Set T) ↔ _
    rw [← hquot x]
    exact hpre _
  have hprePL := hPL.comp
    (locallyPiecewiseAffineOn_affine a.toContinuousAffineEquiv.toContinuousAffineMap isOpen_univ)
  have hpostPL := (locallyPiecewiseAffineOn_affine
    a.symm.toContinuousAffineEquiv.toContinuousAffineMap isOpen_univ).comp hprePL
  refine ⟨⟨a.symm ∘ f ∘ t, a.symm '' K, hK.image a.symm.continuous, hloc, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨f (t x), himage ⟨t x, (hpre x).mpr hx, rfl⟩, rfl⟩
  · intro x hx
    obtain ⟨hne, heq⟩ := hcore x hx
    refine ⟨?_, ?_⟩
    · intro he
      exact hne ((hquot x).symm.trans ((congrArg t he).trans hp))
    · change a.symm (f (t (QuotientAddGroup.mk x))) = x
      rw [hquot, heq, a.symm_apply_apply]
  · have hraw : LocallyPiecewiseAffineOn (fun x => a.symm (f (q (a x))))
        (a ⁻¹' (q ⁻¹' {p}ᶜ)) := by
      simpa only [preimage_univ, inter_univ, univ_inter, Function.comp_def,
        ContinuousAffineEquiv.coe_toContinuousAffineMap,
        ContinuousLinearEquiv.coe_toContinuousAffineEquiv] using hpostPL
    rw [hdomain] at hraw
    apply hraw.congr
    intro x _
    change a.symm (f (q (a x))) = a.symm (f (t (QuotientAddGroup.mk x)))
    rw [hquot]

private theorem circle_raw_PL
    (p : ℝ) [Fact (0 < p)] (e : OpenPartialHomeomorph (AddCircle p) ℝ)
    (hPL : ∀ a, (AddCircle.openPartialHomeomorphCoe p a).trans e ∈
      piecewiseAffineGroupoid ℝ) :
    LocallyPiecewiseAffineOn (fun x : ℝ => e (x : AddCircle p))
      (((↑) : ℝ → AddCircle p) ⁻¹' e.source) := by
  apply LocallyPiecewiseAffineOn.locality
  intro x hx
  let Q := AddCircle.openPartialHomeomorphCoe p (x - p / 2)
  have hxQ : x ∈ Q.source := by
    change x - p / 2 < x ∧ x < x - p / 2 + p
    constructor <;> linarith [Fact.out (p := 0 < p)]
  refine ⟨Q.source, hxQ, ?_⟩
  have h := (mem_piecewiseAffineGroupoid_iff_forward _).mp (hPL (x - p / 2))
  exact h.mono
    ((e.open_source.preimage (AddCircle.continuous_mk' p)).inter Q.open_source)
    (fun _ hy => ⟨hy.2, hy.1⟩)

private theorem torus_raw_PL
    (p : ℝ) [Fact (0 < p)] (z : AddCircle p × AddCircle p)
    (f : (AddCircle p × AddCircle p) → ℝ × ℝ)
    (hPL : ∀ a b,
      let Q := (AddCircle.openPartialHomeomorphCoe p a).prod
        (AddCircle.openPartialHomeomorphCoe p b)
      LocallyPiecewiseAffineOn (f ∘ Q) (Q.source ∩ Q ⁻¹' {z}ᶜ)) :
    LocallyPiecewiseAffineOn (fun x : ℝ × ℝ => f ((x.1 : AddCircle p), (x.2 : AddCircle p)))
      ((fun x : ℝ × ℝ => ((x.1 : AddCircle p), (x.2 : AddCircle p))) ⁻¹' {z}ᶜ) := by
  let q : (ℝ × ℝ) → (AddCircle p × AddCircle p) := fun x =>
    ((x.1 : AddCircle p), (x.2 : AddCircle p))
  have hq : Continuous q :=
    ((AddCircle.continuous_mk' p).comp continuous_fst).prodMk
      ((AddCircle.continuous_mk' p).comp continuous_snd)
  apply LocallyPiecewiseAffineOn.locality
  intro x hx
  let Q := (AddCircle.openPartialHomeomorphCoe p (x.1 - p / 2)).prod
    (AddCircle.openPartialHomeomorphCoe p (x.2 - p / 2))
  have hxQ : x ∈ Q.source := by
    change (x.1 - p / 2 < x.1 ∧ x.1 < x.1 - p / 2 + p) ∧
      (x.2 - p / 2 < x.2 ∧ x.2 < x.2 - p / 2 + p)
    constructor <;> constructor <;> linarith [Fact.out (p := 0 < p)]
  refine ⟨Q.source, hxQ, ?_⟩
  exact (hPL (x.1 - p / 2) (x.2 - p / 2)).mono
    ((isClosed_singleton.isOpen_compl.preimage hq).inter Q.open_source)
    (fun _ hy => ⟨hy.2, hy.1⟩)

private theorem lower_halfperiod_eq :
    ((256 : ℝ) : AddCircle (4 * (128 : ℝ))) = ((-256 : ℝ) : AddCircle (4 * (128 : ℝ))) := by
  convert AddCircle.coe_add_period (4 * (128 : ℝ)) (-256) using 1
  norm_num

theorem exists_lower_lattice_immersion_one :
    Nonempty (HamiltonLowerLatticeImmersion (Fin 1)) := by
  let : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩
  let C := AddCircle (4 * (128 : ℝ))
  let t := (hamiltonLowerLatticePiEquiv (Fin 1)).trans (Homeomorph.funUnique (Fin 1) C)
  let a := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
  obtain ⟨e, K, hs, _, hK, hbound, hcore, hPL⟩ :=
    AddCircle.exists_bounded_core_fixed_puncturedCircle_chart
      (4 * (128 : ℝ)) 3 (by norm_num)
  have hes : e.source = {((256 : ℝ) : C)}ᶜ := by
    rw [hs]
    congr 2
    norm_num
    exact lower_halfperiod_eq.symm
  apply lower_immersion_of_model t a (fun x : ℝ => (x : C)) ((256 : ℝ) : C)
    (fun _ => rfl) rfl e K hK
  · simpa only [hes] using
      IsLocalHomeomorphOn.OpenPartialHomeomorph.isLocalHomeomorphOn e
  · simpa only [hes] using hbound
  · intro x hx
    have hx0 : x 0 ∈ Icc (-3 : ℝ) 3 := by
      have hb := (norm_le_pi_norm x 0).trans hx
      simpa only [Real.norm_eq_abs, abs_le, mem_Icc] using hb
    obtain ⟨hxe, heq⟩ := hcore (x 0) hx0
    refine ⟨?_, heq⟩
    rw [hes] at hxe
    exact hxe
  · simpa only [hes, Function.comp_def] using circle_raw_PL (4 * (128 : ℝ)) e hPL

theorem exists_lower_lattice_immersion_two :
    Nonempty (HamiltonLowerLatticeImmersion (Fin 2)) := by
  let : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩
  let C := AddCircle (4 * (128 : ℝ))
  let t := (hamiltonLowerLatticePiEquiv (Fin 2)).trans (Homeomorph.finTwoArrow (X := C))
  let a := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  let q : (ℝ × ℝ) → C × C := fun x => ((x.1 : C), (x.2 : C))
  let p := AddCircle.centeredSquareQuotient (4 * (128 : ℝ)) 0
  obtain ⟨f, K, hf, hK, himage, hcore, hPL⟩ :=
    PLAnnularStrip.exists_bounded_punctured_torus_PL_immersion
      (L := 128) (d := 8) (D := 16)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hp : t (hamiltonLowerLatticePuncture (Fin 2)) = p := by
    change (((256 : ℝ) : C), ((256 : ℝ) : C)) = p
    simp [p, AddCircle.centeredSquareQuotient_apply]
    norm_num
  apply lower_immersion_of_model t a q p (fun _ => rfl) hp f K hK hf himage
  · intro x hx
    have hxi (i : Fin 2) : |x i| ≤ 3 := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x i).trans hx
    obtain ⟨e, hs, _, hc, _⟩ :=
      AddCircle.exists_core_fixed_puncturedCircle_chart
        (4 * (128 : ℝ)) 3 (by norm_num)
    have hne : ((x 0 : ℝ) : C) ≠ ((256 : ℝ) : C) := by
      have hxsrc := (hc (x 0) (abs_le.mp (hxi 0))).1
      rw [hs] at hxsrc
      intro he
      apply hxsrc
      change ((x 0 : ℝ) : C) = ((-(4 * 128) / 2 : ℝ) : C)
      rw [he, lower_halfperiod_eq]
      norm_num
    refine ⟨?_, ?_⟩
    · intro he
      apply hne
      have he' := congrArg Prod.fst he
      norm_num [q, a, p, AddCircle.centeredSquareQuotient_apply] at he' ⊢
      exact he'
    · exact hcore (x 0) ⟨by linarith [(abs_le.mp (hxi 0)).1],
          by linarith [(abs_le.mp (hxi 0)).2]⟩
        (x 1) ⟨by linarith [(abs_le.mp (hxi 1)).1],
          by linarith [(abs_le.mp (hxi 1)).2]⟩
  · exact torus_raw_PL (4 * (128 : ℝ)) p f hPL

end PoincareConjecture.M76
