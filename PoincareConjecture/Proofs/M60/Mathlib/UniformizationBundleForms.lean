import PoincareConjecture.Proofs.M60.Mathlib.UniformizationPositiveForms
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.RoundMetric
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Set Filter
open scoped Manifold ContDiff Topology

universe u

noncomputable section

namespace PoincareConjecture.M60

local notation "E" => LoopPlane
local notation "T" => TangentSpace (𝓡 2) (M := UnitTwoSphere)
local notation "V" => (fun p : UnitTwoSphere => T p →L[ℝ] T p →L[ℝ] ℝ)

local instance uniformizationTangentNormedAddCommGroup (p : UnitTwoSphere) :
    NormedAddCommGroup (T p) :=
  inferInstanceAs (NormedAddCommGroup E)

local instance uniformizationTangentNormedSpace (p : UnitTwoSphere) : NormedSpace ℝ (T p) :=
  inferInstanceAs (NormedSpace ℝ E)

local instance uniformizationCotangentContinuousAdd :
    ∀ p : UnitTwoSphere, ContinuousAdd (T p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (E →L[ℝ] ℝ))

theorem spherePullbackForm_contMDiffAt_zero
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {f : UnitTwoSphere → M} {p : UnitTwoSphere}
    (hf : ContMDiffAt (𝓡 2) (𝓡 n) 1 f p) :
    ContMDiffAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 0
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x
        (metricPullbackForm (n := 2) g f x)) p := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  let F := EuclideanSpace ℝ (Fin n)
  let TM := TangentSpace (𝓡 n) (M := M)
  let A := inTangentCoordinates (𝓡 2) (𝓡 n) id f (mfderiv (𝓡 2) (𝓡 n) f) p
  let B := fun y => ContinuousLinearMap.inCoordinates F TM (F →L[ℝ] ℝ)
    (fun z => TM z →L[ℝ] ℝ) (f p) y (f p) y (g.inner y)
  have hA : ContMDiffAt (𝓡 2) 𝓘(ℝ, E →L[ℝ] F) 0 A p :=
    hf.mfderiv_const (by norm_num)
  have hB : ContMDiffAt (𝓡 n) 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) 0 B (f p) :=
    (((contMDiffAt_hom_bundle _).mp (g.contMDiff (f p))).2).of_le (by simp)
  have hform := (hA.clm_precomp (F₃ := ℝ)).clm_comp
    ((hB.comp p (hf.of_le (by norm_num))).clm_comp hA)
  apply hform.congr_of_eventuallyEq
  have hx := (trivializationAt E T p).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E T p)
  have hy := hf.continuousAt.preimage_mem_nhds
    ((trivializationAt F TM (f p)).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt F TM (f p)))
  filter_upwards [hx, hy] with x hx hy
  exact metricPullbackForm_coordinates g f hx hy

theorem eventually_positive_sphere_form (B : (p : UnitTwoSphere) → V p)
    {p : UnitTwoSphere}
    (hB : ContinuousAt (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (B x)) p)
    (hpos : ∀ v : T p, v ≠ 0 → 0 < B p v v) :
    ∀ᶠ x in 𝓝 p, ∀ v : T x, v ≠ 0 → 0 < B x v v := by
  let e := trivializationAt E T p
  have hp : p ∈ e.baseSet := mem_baseSet_trivializationAt E T p
  let C := fun x => ContinuousLinearMap.inCoordinates E T (E →L[ℝ] ℝ)
    (fun y => T y →L[ℝ] ℝ) p x p x (B x)
  have hC : ContinuousAt C p := by
    simp only [continuousAt_hom_bundle] at hB
    exact hB.2
  have hC_apply {x : UnitTwoSphere} (hx : x ∈ e.baseSet) (v w : E) :
      C x v w = B x (e.symmL ℝ x v) (e.symmL ℝ x w) := by
    dsimp only [C]
    rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial UnitTwoSphere ℝ) hx hx (by simp)]
    simp only [Bundle.Trivial.eq_trivialization, Bundle.Trivial.linearMapAt_trivialization,
      LinearMap.id_apply]
    change B x (e.symm x v) (e.symm x w) = _
    rw [← e.symmL_apply (R := ℝ) hx, ← e.symmL_apply (R := ℝ) hx]
  have hCp : ∀ v : E, v ≠ 0 → 0 < C p v v := by
    intro v hv
    rw [hC_apply hp]
    apply hpos
    intro hzero
    apply hv
    have h := e.continuousLinearMapAt_symmL (R := ℝ) hp v
    rw [hzero, map_zero] at h
    exact h.symm
  filter_upwards [eventually_positive_bilinear hC hCp, e.open_baseSet.mem_nhds hp]
    with x hx hxe
  intro v hv
  have hne : e.continuousLinearMapAt ℝ x v ≠ 0 := by
    intro hzero
    apply hv
    have h := e.symmL_continuousLinearMapAt (R := ℝ) hxe v
    rw [hzero, map_zero] at h
    exact h.symm
  have h := hx (e.continuousLinearMapAt ℝ x v) hne
  rw [hC_apply hxe, e.symmL_continuousLinearMapAt (R := ℝ) hxe] at h
  exact h

theorem exists_local_smooth_symmetric_sphere_form (p : UnitTwoSphere) (B : V p)
    (hB : ∀ v w, B v w = B w v) :
    ∃ U ∈ 𝓝 p, ∃ s : (x : UnitTwoSphere) → V x,
      ContMDiffOn (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (s x)) U ∧
      s p = B ∧ ∀ x ∈ U, ∀ v w, s x v w = s x w v := by
  classical
  let e := trivializationAt E T p
  have hp : p ∈ e.baseSet := mem_baseSet_trivializationAt E T p
  let e₀ := e.continuousLinearEquivAt ℝ p hp
  let B₀ := (e₀.arrowCongr (e₀.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))) B
  have hB₀ (v w : E) : B₀ v w = B (e₀.symm v) (e₀.symm w) := rfl
  let s : (x : UnitTwoSphere) → V x := fun x =>
    if hx : x ∈ e.baseSet then
      ((e.continuousLinearEquivAt ℝ x hx).symm.arrowCongr
        ((e.continuousLinearEquivAt ℝ x hx).symm.arrowCongr
          (ContinuousLinearEquiv.refl ℝ ℝ))) B₀
    else 0
  have hs_apply (x : UnitTwoSphere) (hx : x ∈ e.baseSet) (v w : T x) :
      s x v w = B₀ (e.continuousLinearEquivAt ℝ x hx v)
        (e.continuousLinearEquivAt ℝ x hx w) := by
    simp only [s, dif_pos hx]
    rfl
  refine ⟨e.baseSet, e.open_baseSet.mem_nhds hp, s, ?_, ?_, ?_⟩
  · have hbase : (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ) V p).baseSet = e.baseSet := by
      simp only [hom_trivializationAt_baseSet, Bundle.Trivial.eq_trivialization,
        Bundle.Trivial.trivialization, Set.inter_univ, Set.inter_self]
      rfl
    rw [← hbase, Bundle.Trivialization.contMDiffOn_section_baseSet_iff]
    refine (contMDiffOn_const (c := B₀)).congr ?_
    intro x hx
    rw [hbase] at hx
    ext v w
    simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
      ContinuousLinearMap.comp_apply]
    have hx₂ : x ∈ (trivializationAt (E →L[ℝ] ℝ)
        (fun z => T z →L[ℝ] ℝ) p).baseSet := by
      rw [hom_trivializationAt_baseSet]
      exact ⟨hx, Set.mem_univ x⟩
    rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ
      (trivializationAt (E →L[ℝ] ℝ) (fun z => T z →L[ℝ] ℝ) p) hx₂]
    simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
      ContinuousLinearMap.comp_apply]
    simp only [Bundle.Trivial.eq_trivialization,
      Bundle.Trivial.continuousLinearMapAt_trivialization,
      ContinuousLinearMap.id_apply, hs_apply x hx]
    change B₀ ((e.continuousLinearEquivAt ℝ x hx) (e.symmL ℝ x v))
      ((e.continuousLinearEquivAt ℝ x hx) (e.symmL ℝ x w)) = B₀ v w
    simp only [← Trivialization.symm_continuousLinearEquivAt_eq' e hx,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  · ext v w
    rw [hs_apply p hp, hB₀]
    exact congrArg₂ (fun v w => B v w) (e₀.symm_apply_apply v) (e₀.symm_apply_apply w)
  · intro x hx v w
    rw [hs_apply x hx, hs_apply x hx, hB₀, hB₀, hB]

end PoincareConjecture.M60

end
