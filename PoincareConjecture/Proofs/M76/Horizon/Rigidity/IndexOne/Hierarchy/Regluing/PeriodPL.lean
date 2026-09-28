import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Regluing.PeriodPLParameters
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "W" => (V2 × ℝ)
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L

private instance : Fact (0 < p) := ⟨by norm_num⟩

private theorem exists_period_short_chart (x : C) :
    ∃ (l u : ℝ) (c : OpenPartialHomeomorph ℝ C),
      l < u ∧ u < l + p ∧ x ∈ c.target ∧ c.symm x ∈ Ioo l u ∧
      (∀ t, c t = (t : C)) ∧ ((l = -1 ∧ u = 1) ∨ (0 < l ∧ u < p)) := by
  obtain ⟨t, ht, htx⟩ := AddCircle.eq_coe_Ico x
  by_cases ht0 : t = 0
  · subst t
    let c := AddCircle.openPartialHomeomorphCoe p (-2)
    have htS : (0 : ℝ) ∈ c.source := by change 0 ∈ Ioo (-2 : ℝ) (-2 + p); norm_num
    have hc0 : c 0 = x := htx
    have hInv : c.symm x = 0 := by rw [← hc0]; exact c.left_inv htS
    refine ⟨-1, 1, c, by norm_num, by norm_num, ?_, ?_, fun _ => rfl, Or.inl ⟨rfl, rfl⟩⟩
    · rw [← hc0]; exact c.map_source htS
    · rw [hInv]; norm_num
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    let c := AddCircle.openPartialHomeomorphCoe p 0
    have htS : t ∈ c.source := by change t ∈ Ioo 0 (0 + p); simpa using ⟨htpos, ht.2⟩
    have hct : c t = x := htx
    have hInv : c.symm x = t := by rw [← hct]; exact c.left_inv htS
    refine ⟨t / 2, (t + p) / 2, c, by linarith, by linarith, ?_, ?_,
      fun _ => rfl, Or.inr ⟨by linarith, by linarith [ht.2]⟩⟩
    · rw [← hct]; exact c.map_source htS
    · rw [hInv]; constructor <;> linarith [ht.2]

theorem polyhedralPL_slab_parameter_of_period
    {E Y α β : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace Y] {e : α → OpenPartialHomeomorph Y V3}
    {d : β → OpenPartialHomeomorph X V3} {N : Set Y}
    (he : PLDomain e N) (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (a b : ℝ) (hab : a < b) (hshort : b < a + p)
    (G : C(D × C, Y)) (g : W → Y)
    (hg : PolyhedralPLInCharts e g (D ×ˢ Icc 0 p))
    (hwhole : ∀ z : D, ∀ t ∈ Icc (0 : ℝ) p, G (z, (t : C)) = g (z, t))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (r : E → sourceSlab (ContinuousMap.id H) a b)
    (hr : PolyhedralPLInCharts d (fun z => (r z : X)) K.space) :
    PolyhedralPLInCharts e
      (fun z => G ((standardSlabMeridianCoordinates a b hab hshort).symm (r z))) K.space := by
  let T := standardSlabMeridianCoordinates a b hab hshort
  let s : E → D × C := fun z => T.symm (r z)
  have hrc : ContinuousOn r K.space :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr hr.continuousOn
  have hs : ContinuousOn s K.space := T.symm.continuous.comp_continuousOn hrc
  have hperiod : PolyhedralPLInCharts e (G ∘ diskCircleParameter) (D ×ˢ Icc 0 p) :=
    hg.congr (by
      intro z hz
      rw [Function.comp_apply, diskCircleParameter_apply z.1 hz.1]
      exact (hwhole ⟨z.1, hz.1⟩ z.2 hz.2).symm)
  have hsigned := polyhedralPL_diskCircle_signed_parameter he G hperiod
  change PolyhedralPLInCharts e (fun z => G (s z)) K.space
  refine ⟨G.continuous.comp_continuousOn hs, ?_⟩
  intro x
  obtain ⟨l, u, c, hlu, hwidth, hxC, hxI, hcval, hcase⟩ := exists_period_short_chart (s x).2
  let O : Set K.space := (fun y : K.space => (s y).2) ⁻¹'
    (c.target ∩ c.symm ⁻¹' Ioo l u)
  have hO : IsOpen O := (c.symm.isOpen_inter_preimage isOpen_Ioo).preimage
    (continuous_snd.comp hs.domRestrict)
  obtain ⟨J, V, hJ, hJK, hV, hxV, hVJ, hJO⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x hO ⟨hxC, hxI⟩
  have hlocal (y : E) (hy : y ∈ J.space) :
      (s y).2 ∈ c.target ∧ c.symm (s y).2 ∈ Ioo l u := hJO (a := ⟨y, hJK hy⟩) hy
  let lift : E → W := fun y => ((s y).1, c.symm (s y).2)
  have hlc : ContinuousOn lift J.space :=
    (continuous_subtype_val.comp_continuousOn (continuous_fst.comp_continuousOn
      (hs.mono hJK))).prodMk
      (c.symm.continuousOn.comp (continuous_snd.comp_continuousOn (hs.mono hJK))
        (fun y hy => (hlocal y hy).1))
  have hlmap : MapsTo lift J.space (D ×ˢ Icc l u) :=
    fun y hy => ⟨(s y).1.property, Ioo_subset_Icc_self (hlocal y hy).2⟩
  have hcoordinates (y : E) (hy : y ∈ J.space) : diskCircleParameter (lift y) = s y := by
    rw [diskCircleParameter_apply (s y).1 (s y).1.property]
    apply Prod.ext
    · rfl
    · exact (hcval _).symm.trans (c.right_inv (hlocal y hy).1)
  have htarget (y : E) (hy : y ∈ J.space) :
      standardMeridianBandParameter a b (lift y) = (r y : X) := by
    have hh : standardMeridianBandParameter a b (lift y) =
        (T (diskCircleParameter (lift y)) : X) := by
      rw [diskCircleParameter_apply (s y).1 (s y).1.property]
      exact (standardSlabMeridianCoordinates_coe a b hab hshort (s y).1 _).symm
    rw [hh, hcoordinates y hy]
    exact congrArg Subtype.val (T.apply_symm_apply (r y))
  have hlPL : FinitePiecewiseAffineOn lift J.space :=
    (polyhedralPL_standardMeridianBoxParameter hd a b hlu).finitePiecewiseAffineOn_lift
      hd.domain.compatible (injOn_standardMeridianBoxParameter a b hab hshort hwidth)
      J hJ hlc hlmap ((hr.restrict_finite J hJ hJK).congr (fun y hy => (htarget y hy).symm))
  have hboxPL : PolyhedralPLInCharts e (G ∘ diskCircleParameter) (D ×ˢ Icc l u) := by
    rcases hcase with ⟨rfl, rfl⟩ | ⟨hl, hu⟩
    · exact hsigned
    · obtain ⟨B, hB, hBS⟩ := exists_finite_hamiltonMeridianBox hlu
      exact hBS ▸ hperiod.restrict_finite B hB (by
        intro y hy
        obtain ⟨hyD, hyl, hyu⟩ := hBS.subset hy
        exact ⟨hyD, (hl.trans_le hyl).le, (hyu.trans_lt hu).le⟩)
  have hPL : PolyhedralPLInCharts e (fun y => G (s y)) J.space :=
    (hboxPL.comp_finitePiecewiseAffineOn J hJ hlPL hlmap).congr
      (fun y hy => congrArg G (hcoordinates y hy))
  have hxJ : (x : E) ∈ J.space := hVJ ⟨x, hxV, rfl⟩
  obtain ⟨i, A, U, hA, hAJ, hU, hxU, hUA, hfi, hformula⟩ := hPL.coordinates ⟨x, hxJ⟩
  obtain ⟨Z, hZ, hZU⟩ := isOpen_induced_iff.mp hU
  have hxZ : (x : E) ∈ Z := by
    change (⟨x, hxJ⟩ : J.space) ∈ Subtype.val ⁻¹' Z
    rw [hZU]
    exact hxU
  refine ⟨i, A, V ∩ (Subtype.val : K.space → E) ⁻¹' Z, hA, hAJ.trans hJK,
    hV.inter (hZ.preimage continuous_subtype_val), ⟨hxV, hxZ⟩, ?_, hfi, hformula⟩
  rintro y ⟨z, hz, rfl⟩
  have hzJ : (z : E) ∈ J.space := hVJ ⟨z, hz.1, rfl⟩
  apply hUA
  refine ⟨⟨z, hzJ⟩, ?_, rfl⟩
  rw [← hZU]
  exact hz.2

end PoincareConjecture.M76.HamiltonIntervalTorus
