import PoincareConjecture.Proofs.M35.Thm12_28.SphereCoordinates
import PoincareConjecture.Proofs.M35.Thm12_28.PolarCoordinates
import PoincareConjecture.Proofs.M35.Mathlib.FiniteJetComposition
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.ContDiff.Comp










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩



noncomputable def sphereChartFrame (q : UnitTwoSphere) : E2 →L[ℝ] E3 :=
  (ℝ ∙ (-q : E3))ᗮ.subtypeL.comp
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ)
      2 (ne_zero_of_mem_unit_sphere (-q))).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap


theorem sphereChartFrame_norm (q : UnitTwoSphere) (p : E2) :
    ‖sphereChartFrame q p‖ = ‖p‖ :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ)
    2 (ne_zero_of_mem_unit_sphere (-q))).repr.symm.norm_map p


theorem sphereChartFrame_orthogonal (q : UnitTwoSphere) (p : E2) :
    inner ℝ (q : E3) (sphereChartFrame q p) = 0 := by
  have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    ((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ)
      2 (ne_zero_of_mem_unit_sphere (-q))).repr.symm p).property
  change inner ℝ (-q : E3) (sphereChartFrame q p) = 0 at h
  simpa only [inner_neg_left, neg_eq_zero] using h


theorem sphere_chart_inverse_eq_frame (q : UnitTwoSphere) (p : E2) :
    ((chartAt E2 q).symm p).val = stereoInvFunAux (-q : E3) (sphereChartFrame q p) := rfl

private theorem continuous_spatial_jet
    {A X Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : A × X → Y} (hf : ContDiff ℝ ∞ f) (r : ℕ) :
    Continuous (fun p : A × X => iteratedFDeriv ℝ r (fun x => f (p.1, x)) p.2) := by
  let L := ContinuousLinearMap.inr ℝ A X
  have hrepr (p : A × X) :
      iteratedFDeriv ℝ r (fun x => f (p.1, x)) p.2 =
        (iteratedFDeriv ℝ r f p).compContinuousLinearMap (fun _ => L) := by
    have hs := hf.comp ((contDiff_const (c := (p.1, (0 : X)))).add contDiff_id)
    have h := L.iteratedFDeriv_comp_right hs p.2
      (i := r) (by exact_mod_cast le_top (a := (r : ℕ∞)))
    dsimp only [Function.comp_def, id_eq] at h
    rw [iteratedFDeriv_comp_add_left] at h
    simpa only [L, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] using h
  have hc := (hf.iteratedFDeriv_right (m := 0) (i := r) (by
    rw [zero_add]
    exact_mod_cast le_top (a := (r : ℕ∞)))).continuous
  exact ((ContinuousMultilinearMap.compContinuousLinearMapL
    (F := Y) (fun _ : Fin r => L)).continuous.comp hc).congr (fun p => (hrepr p).symm)

private theorem spatial_jets_tendsto_uniformly
    {A X Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : A × X → Y} (hf : ContDiff ℝ ∞ f)
    {a : ℕ → A} {a₀ : A} (ha : Tendsto a atTop (𝓝 a₀))
    (r : ℕ) {K : Set X} (hK : IsCompact K) :
    TendstoUniformlyOn (fun k x => iteratedFDeriv ℝ r (fun y => f (a k, y)) x)
      (fun x => iteratedFDeriv ℝ r (fun y => f (a₀, y)) x) atTop K := by
  have hc := continuous_spatial_jet hf r
  have hu := ((isCompact_closedBall a₀ 1).prod hK).uniformContinuousOn_of_continuous
    hc.continuousOn
  have ht := hu.tendstoUniformlyOn
    (F := fun a x => iteratedFDeriv ℝ r (fun y => f (a, y)) x)
    (Metric.mem_closedBall_self zero_le_one)
  rw [nhdsWithin_eq_nhds.mpr (Metric.closedBall_mem_nhds a₀ zero_lt_one)] at ht
  intro entourage hentourage
  exact ha.eventually (ht entourage hentourage)

private theorem contDiff_frame_inverse :
    ContDiff ℝ ∞ (fun p : (E3 × (E2 →L[ℝ] E3)) × E2 =>
      stereoInvFunAux (-p.1.1) (p.1.2 p.2)) := by
  have hw : ContDiff ℝ ∞ (fun p : (E3 × (E2 →L[ℝ] E3)) × E2 => p.1.2 p.2) :=
    contDiff_fst.snd.clm_apply contDiff_snd
  have hn := (contDiff_norm_sq ℝ).comp hw
  exact ((hn.add (contDiff_const (c := (4 : ℝ)))).inv (fun p => by
    change ‖p.1.2 p.2‖ ^ 2 + 4 ≠ 0
    positivity)).smul
    (((contDiff_const (c := (4 : ℝ))).smul hw).add
      ((hn.sub (contDiff_const (c := (4 : ℝ)))).smul contDiff_fst.fst.neg))




theorem sphere_chart_inverse_subsequence (q : ℕ → UnitTwoSphere) :
    ∃ q₀ : UnitTwoSphere, ∃ L : E2 →L[ℝ] E3, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ Tendsto (q ∘ phi) atTop (𝓝 q₀) ∧
      Tendsto (fun k => sphereChartFrame (q (phi k))) atTop (𝓝 L) ∧
      (∀ p : E2, ‖L p‖ = ‖p‖ ∧ inner ℝ (q₀ : E3) (L p) = 0) ∧
      ∀ r : ℕ, ∀ K : Set E2, IsCompact K →
        TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ r (fun p => ((chartAt E2 (q (phi k))).symm p).val))
          (iteratedFDeriv ℝ r (fun p => stereoInvFunAux (-q₀ : E3) (L p))) atTop K := by
  have hframe (z : UnitTwoSphere) : ‖sphereChartFrame z‖ ≤ 1 :=
    (sphereChartFrame z).opNorm_le_bound zero_le_one (fun p => by
      rw [sphereChartFrame_norm, one_mul])
  have hcompact : IsCompact ((univ : Set UnitTwoSphere) ×ˢ
      Metric.closedBall (0 : E2 →L[ℝ] E3) 1) :=
    isCompact_univ.prod (isCompact_closedBall _ _)
  obtain ⟨a, _, phi, hphi, hconv⟩ := hcompact.tendsto_subseq
    (x := fun k => (q k, sphereChartFrame (q k)))
    (fun k => ⟨mem_univ _, by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hframe (q k)⟩)
  have hq : Tendsto (q ∘ phi) atTop (𝓝 a.1) := continuous_fst.tendsto a |>.comp hconv
  have hL : Tendsto (fun k => sphereChartFrame (q (phi k))) atTop (𝓝 a.2) :=
    continuous_snd.tendsto a |>.comp hconv
  have hqa : Tendsto (fun k => ((q (phi k) : UnitTwoSphere) : E3)) atTop (𝓝 (a.1 : E3)) :=
    continuous_subtype_val.continuousAt.tendsto.comp hq
  refine ⟨a.1, a.2, phi, hphi, hq, hL, ?_, ?_⟩
  · intro p
    have hv : Tendsto (fun k => sphereChartFrame (q (phi k)) p) atTop (𝓝 (a.2 p)) :=
      ((ContinuousLinearMap.apply ℝ E3 p).continuous.tendsto a.2).comp hL
    refine ⟨?_, ?_⟩
    · apply tendsto_nhds_unique hv.norm
      simpa only [sphereChartFrame_norm] using (tendsto_const_nhds (x := ‖p‖))
    · apply tendsto_nhds_unique (hqa.inner hv)
      simpa only [sphereChartFrame_orthogonal] using (tendsto_const_nhds (x := (0 : ℝ)))
  · intro r K hK
    have hparam := hqa.prodMk_nhds hL
    have hjet := spatial_jets_tendsto_uniformly contDiff_frame_inverse hparam r hK
    simpa only [sphere_chart_inverse_eq_frame] using hjet



theorem sphere_cylinder_inverse_jet_tendsto
    (q : ℕ → UnitTwoSphere) (q₀ : UnitTwoSphere) (L : E2 →L[ℝ] E3)
    (hq : Tendsto q atTop (𝓝 q₀))
    (hL : Tendsto (fun k => sphereChartFrame (q k)) atTop (𝓝 L))
    (s : ℕ → ℝ) (s₀ : ℝ) (hs : Tendsto s atTop (𝓝 s₀)) (r : ℕ) :
    Tendsto (fun k => iteratedFDeriv ℝ r (fun p : RoundCylinderCoordinates =>
      (((chartAt E2 (q k)).symm p.1).val, p.2)) (0, s k)) atTop
      (𝓝 (iteratedFDeriv ℝ r (fun p : RoundCylinderCoordinates =>
        (stereoInvFunAux (-q₀ : E3) (L p.1), p.2)) (0, s₀))) := by
  have hF : ContDiff ℝ ∞
      (fun p : (E3 × (E2 →L[ℝ] E3)) × RoundCylinderCoordinates =>
        (stereoInvFunAux (-p.1.1) (p.1.2 p.2.1), p.2.2)) :=
    (contDiff_frame_inverse.comp (contDiff_fst.prodMk contDiff_snd.fst)).prodMk contDiff_snd.snd
  have hqa := continuous_subtype_val.continuousAt.tendsto.comp hq
  have h := ((continuous_spatial_jet hF r).tendsto ((q₀.val, L), (0, s₀))).comp
    ((hqa.prodMk_nhds hL).prodMk_nhds (tendsto_const_nhds.prodMk_nhds hs))
  simpa only [Function.comp_def, sphere_chart_inverse_eq_frame] using h



theorem sphere_cylinder_radial_extension_contDiffAt
    (q₀ q : UnitTwoSphere) (s : ℝ) (H : RoundCylinderSpace → E3)
    (hH : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ H (q, s)) :
    ContDiffAt ℝ ∞ (fun p : E3 × ℝ => H ((spherePolarMap q₀ p.1).1, p.2)) (q.val, s) := by
  have hfst : ContMDiffAt 𝓘(ℝ, E3 × ℝ) (𝓡 3) ∞ Prod.fst (q.val, s) :=
    contDiffAt_fst.contMDiffAt
  have hsnd : ContMDiffAt 𝓘(ℝ, E3 × ℝ) 𝓘(ℝ, ℝ) ∞ Prod.snd (q.val, s) :=
    contDiffAt_snd.contMDiffAt
  have hrad : ContMDiffAt 𝓘(ℝ, E3 × ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : E3 × ℝ => ((spherePolarMap q₀ p.1).1, p.2)) (q.val, s) :=
    (((spherePolarMap_contMDiffAt q₀ (ne_zero_of_mem_unit_sphere q)).comp
      (q.val, s) hfst).fst).prodMk hsnd
  have hH' : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ H
      ((spherePolarMap q₀ q.val).1, s) := by
    simpa only [spherePolarMap_sphere] using hH
  exact (hH'.comp (q.val, s) hrad).contDiffAt




theorem sphere_cylinder_composed_jets_tendsto
    (q : ℕ → UnitTwoSphere) (q₀ : UnitTwoSphere) (L : E2 →L[ℝ] E3)
    (hq : Tendsto q atTop (𝓝 q₀))
    (hL : Tendsto (fun k => sphereChartFrame (q k)) atTop (𝓝 L))
    (s : ℕ → ℝ) (s₀ : ℝ) (hs : Tendsto s atTop (𝓝 s₀))
    (H : RoundCylinderSpace → E3)
    (hH₀ : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ H (q₀, s₀))
    (hH : ∀ᶠ k in atTop, ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ H (q k, s k))
    (r : ℕ) :
    Tendsto (fun k => iteratedFDeriv ℝ r (fun p : RoundCylinderCoordinates =>
      H ((chartAt E2 (q k)).symm p.1, p.2)) (0, s k)) atTop
      (𝓝 (iteratedFDeriv ℝ r (fun p : RoundCylinderCoordinates =>
        H ((spherePolarMap q₀ (stereoInvFunAux (-q₀ : E3) (L p.1))).1, p.2)) (0, s₀))) := by
  let F (k : ℕ) (p : RoundCylinderCoordinates) := (((chartAt E2 (q k)).symm p.1).val, p.2)
  let F₀ (p : RoundCylinderCoordinates) := (stereoInvFunAux (-q₀ : E3) (L p.1), p.2)
  let G (p : E3 × ℝ) := H ((spherePolarMap q₀ p.1).1, p.2)
  have hF₀ : ContDiff ℝ ∞ F₀ :=
    (contDiff_stereoInvFunAux.comp (L.contDiff.comp contDiff_fst)).prodMk contDiff_snd
  have hF (k : ℕ) : ContDiff ℝ ∞ (F k) := by
    change ContDiff ℝ ∞ (fun p : RoundCylinderCoordinates =>
      (stereoInvFunAux (-q k : E3) (sphereChartFrame (q k) p.1), p.2))
    exact (contDiff_stereoInvFunAux.comp
      ((sphereChartFrame (q k)).contDiff.comp contDiff_fst)).prodMk contDiff_snd
  have hfzero : F₀ (0, s₀) = (q₀.val, s₀) := by
    simp [F₀, stereoInvFunAux, smul_smul]
  have hfcenter (k : ℕ) : F k (0, s k) = ((q k).val, s k) := by
    have hc := (chartAt E2 (q k)).left_inv (mem_chart_source E2 (q k))
    rw [sphere_chart_center] at hc
    exact Prod.ext (congrArg Subtype.val hc) rfl
  have hG₀ : ContDiffAt ℝ ∞ G (F₀ (0, s₀)) := by
    rw [hfzero]
    exact sphere_cylinder_radial_extension_contDiffAt q₀ q₀ s₀ H hH₀
  have hG : ∀ᶠ k in atTop, ContDiffAt ℝ ∞ G (F k (0, s k)) := by
    filter_upwards [hH] with k hk
    rw [hfcenter]
    exact sphere_cylinder_radial_extension_contDiffAt q₀ (q k) (s k) H hk
  have hpoints : Tendsto (fun k => F k (0, s k)) atTop (𝓝 (F₀ (0, s₀))) := by
    simp_rw [hfcenter, hfzero]
    exact (continuous_subtype_val.continuousAt.tendsto.comp hq).prodMk_nhds hs
  have hcomp := tendsto_iteratedFDeriv_comp_of_jets
    (f := F) (g := fun _ => G) (f₀ := F₀) (g₀ := G) (p := fun k => (0, s k)) r
    hF₀.contDiffAt hG₀ (Eventually.of_forall fun k => (hF k).contDiffAt) hG
    (fun m _ => sphere_cylinder_inverse_jet_tendsto q q₀ L hq hL s s₀ hs m)
    (fun m _ => (hG₀.continuousAt_iteratedFDeriv (by
      exact_mod_cast le_top (a := (m : ℕ∞)))).tendsto.comp hpoints)
  simpa only [F, F₀, G, Function.comp_def, spherePolarMap_sphere] using hcomp

end PoincareConjecture.M35
