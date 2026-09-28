import PoincareConjecture.Statements.M66
import PoincareConjecture.Proofs.M60.Filling
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity








set_option autoImplicit false
open scoped Manifold ContDiff Bundle Topology ENNReal intervalIntegral
universe u
namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

private theorem fillingArea_nonnegative (g : RiemannianMetric 3 M)
    (c : C1FreeLoopSpace (M := M)) : 0 ≤ fillingArea g c := by
  apply Real.sInf_nonneg
  rintro a ⟨D, rfl⟩
  exact D.area_nonnegative

private theorem profile_affine {a b : ℝ} (F : RicciFlow 3 M (Set.Icc a b))
    (w d t : ℝ) :
    areaComparisonProfile F (w + d) t = areaComparisonProfile F w t +
      Real.exp (-(∫ s in a..t, flowScalarCurvatureInfimum F s / 2)) * d := by
  unfold areaComparisonProfile flowScalarCurvatureInfimum
  ring

private theorem profile_mono {a b : ℝ} (F : RicciFlow 3 M (Set.Icc a b))
    {w v : ℝ} (h : w ≤ v) (t : ℝ) :
    areaComparisonProfile F w t ≤ areaComparisonProfile F v t := by
  unfold areaComparisonProfile
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right h _) (Real.exp_pos _).le





theorem m66_deformed_comparison
    (hM61 : M61RawWidthCore.{u})
    (hM58 : RepairedShortLoopTrivialityTheory.{u})
    {hM64 : M64ComparisonTheory.{u}}
    (hM65 : M65DeformationTheory hM61 hM64)
    {a b : ℝ} (P : M65RawFlowInput M a b)
    (hconnected : IsConnected (Set.univ : Set M)) (basepoint : M)
    (hpi : Subsingleton (HomotopyGroup.Pi 2 M basepoint))
    (hnontrivial : ¬ P.family.Homotopic (constantLoopFamily basepoint))
    (e eta : ℝ) (he : 0 < e) (heta : 0 < eta) :
    let A := areaComparisonProfile P.flow
      (m61FreeClassWidth (P.flow.metric a) P.family) b
    let E := Real.exp (-(∫ s in a..b, flowScalarCurvatureInfimum P.flow s / 2))
    0 ≤ A + (2 * E + 1) * e ∧
      m61FreeClassWidth (P.flow.metric b) P.family ≤
        max eta (A + (2 * E + 1) * e) := by
  classical
  let : T2Space M := P.hausdorff
  let : SecondCountableTopology M := P.second_countable
  dsimp only
  let A := areaComparisonProfile P.flow
    (m61FreeClassWidth (P.flow.metric a) P.family) b
  let E := Real.exp (-(∫ s in a..b, flowScalarCurvatureInfimum P.flow s / 2))
  have hE : 0 < E := Real.exp_pos _
  obtain ⟨G, hGn, hGh, hG⟩ :=
    (hM61.free_class (P.flow.metric a) P.compact P.family P.family_null).near_minimizer e he
  obtain ⟨r, hr, hshort⟩ := hM58.short_loop.raw_short_loop_family_trivial
    (P.flow.metric b) P.compact hconnected basepoint hpi
  obtain ⟨q, hq, _, hsmall⟩ :=
    hM58.short_loop.small_loop_filling (P.flow.metric b) P.compact eta heta
  let z := min e (min r q)
  have hz : 0 < z := lt_min he (lt_min hr hq)
  have hze : z ≤ e := min_le_left _ _
  have hzr : z ≤ r := (min_le_right _ _).trans (min_le_left _ _)
  have hzq : z ≤ q := (min_le_right _ _).trans (min_le_right _ _)
  let Q : M65RawFlowInput M a b := { P with family := G, family_null := hGn }
  obtain ⟨K⟩ := hM65 M Q
  obtain ⟨D⟩ := K.deformation z hz
  let ta : Set.Icc a b := ⟨a, le_rfl, P.time_ordered⟩
  let tb : Set.Icc a b := ⟨b, P.time_ordered, le_rfl⟩
  have hhom : P.family.Homotopic (D.family tb) :=
    hGh.trans (D.free_homotopy_to_initial tb)
  have hpoint : ∀ c, areaComparisonProfile P.flow
      (fillingArea (P.flow.metric a) (D.family ta c)) b + z ≤
      A + (2 * E + 1) * e := by
    intro c
    have hinit := (abs_lt.mp (D.initial_area_close c)).2
    have hsup : fillingArea (P.flow.metric a) (G c) ≤
        m61FamilyWidth (P.flow.metric a) G :=
      le_csSup (hM61.family (P.flow.metric a) P.compact G hGn).bounded_above
        (Set.mem_range_self c)
    have hc : fillingArea (P.flow.metric a) (D.family ta c) ≤
        m61FreeClassWidth (P.flow.metric a) P.family + (e + z) := by
      change fillingArea (P.flow.metric a) (D.family ta c) -
        fillingArea (P.flow.metric a) (G c) < z at hinit
      linarith
    have hp := profile_mono P.flow hc b
    rw [profile_affine] at hp
    change areaComparisonProfile P.flow
      (fillingArea (P.flow.metric a) (D.family ta c)) b ≤ A + E * (e + z) at hp
    nlinarith
  have hlong : ∃ c, ¬ freeLoopLength (P.flow.metric b) (D.family tb c) < z := by
    by_contra! hall
    exact hnontrivial (hhom.trans
      (hshort (D.family tb) (D.null tb) (fun c => (hall c).trans_le hzr)))
  obtain ⟨c, hc⟩ := hlong
  have hbound := (D.terminal_alternative c).resolve_left hc
  have hnonneg : 0 ≤ A + (2 * E + 1) * e :=
    (fillingArea_nonnegative (P.flow.metric b) (D.family tb c)).trans
      (hbound.trans (hpoint c))
  refine ⟨hnonneg, ?_⟩
  apply (hM61.free_class (P.flow.metric b) P.compact P.family P.family_null).le_member
    (D.family tb) (D.null tb) hhom |>.trans
  obtain ⟨c, hc⟩ := (hM61.family (P.flow.metric b) P.compact
    (D.family tb) (D.null tb)).attained
  rw [← hc]
  rcases D.terminal_alternative c with hs | hl
  · obtain ⟨disk, hdisk⟩ := hsmall (D.family tb c) (hs.trans_le hzq)
    exact ((m60FillingArea_le_disk _ _ disk).trans hdisk.le).trans (le_max_left _ _)
  · exact (hl.trans (hpoint c)).trans (le_max_right _ _)



theorem m66_endpoint_comparison
    (hM61 : M61RawWidthCore.{u})
    (hM58 : RepairedShortLoopTrivialityTheory.{u})
    {hM64 : M64ComparisonTheory.{u}}
    (hM65 : M65DeformationTheory hM61 hM64)
    {a b : ℝ} (P : M65RawFlowInput M a b)
    (hconnected : IsConnected (Set.univ : Set M)) (basepoint : M)
    (hpi : Subsingleton (HomotopyGroup.Pi 2 M basepoint))
    (hnontrivial : ¬ P.family.Homotopic (constantLoopFamily basepoint)) :
    m61FreeClassWidth (P.flow.metric b) P.family ≤
      areaComparisonProfile P.flow
        (m61FreeClassWidth (P.flow.metric a) P.family) b := by
  let A := areaComparisonProfile P.flow
    (m61FreeClassWidth (P.flow.metric a) P.family) b
  let E := Real.exp (-(∫ s in a..b, flowScalarCurvatureInfimum P.flow s / 2))
  have hE : 0 < 2 * E + 1 := by dsimp [E]; positivity
  have hA : 0 ≤ A := by
    by_contra! hneg
    have h := (m66_deformed_comparison hM61 hM58 hM65 P hconnected basepoint hpi hnontrivial
      (-A / (2 * (2 * E + 1))) 1
      (div_pos (neg_pos.mpr hneg) (mul_pos (by norm_num) hE)) zero_lt_one).1
    change 0 ≤ A + (2 * E + 1) * (-A / (2 * (2 * E + 1))) at h
    field_simp at h
    nlinarith
  apply le_of_forall_pos_le_add
  intro eps heps
  have h := (m66_deformed_comparison hM61 hM58 hM65 P hconnected basepoint hpi hnontrivial
    (eps / (2 * E + 1)) eps (div_pos heps hE) heps).2
  change _ ≤ max eps (A + (2 * E + 1) * (eps / (2 * E + 1))) at h
  have heq : (2 * E + 1) * (eps / (2 * E + 1)) = eps :=
    mul_div_cancel₀ _ (ne_of_gt hE)
  rw [heq] at h
  exact h.trans (max_le (by linarith) le_rfl)

end PoincareConjecture
