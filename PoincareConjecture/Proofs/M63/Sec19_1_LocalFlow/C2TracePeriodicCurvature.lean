import PoincareConjecture.Proofs.M63.Adapters
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessEmbeddedCurve
import PoincareConjecture.Proofs.M62.Lemma19_6_InteriorRegularity
import PoincareConjecture.Proofs.M08.SecondVariationCoordinates
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.CompactOpen

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι

theorem embeddedCurvature_closed_periodic_data
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M) (hab : a < b)
    (hc : M62ShrinkingCurve F c) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e) :
    let H : ℝ → ℝ → W := fun t x =>
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x)
    (∀ t ∈ Icc a b, Function.Periodic (H t) curvePeriod) ∧
    ContinuousOn (fun z : ℝ × ℝ => H z.2 z.1) (univ ×ˢ Icc a b) ∧
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => H z.2 z.1) (univ ×ˢ Ioo a b) := by
  dsimp only
  let H : ℝ → ℝ → W := fun t x =>
    mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x)
  have hpush : ContMDiff ((𝓡 n).prod (𝓡 n)) 𝓘(ℝ, W) ∞
      (fun p : TangentBundle (𝓡 n) M => (mfderiv (𝓡 n) 𝓘(ℝ, W) e p.1 p.2 : W)) :=
    (contMDiff_snd_tangentBundle_modelSpace (n := ∞) W 𝓘(ℝ, W)).comp
      (he.contMDiff_tangentMap (by simp))
  have hclosed : ContinuousOn (fun z : ℝ × ℝ => H z.2 z.1) (univ ×ˢ Icc a b) :=
    hpush.continuous.comp_continuousOn hc.curvature_continuous
  have hsmooth : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => H z.2 z.1)
      (univ ×ˢ Ioo a b) :=
    (hpush.comp_contMDiffOn (M62.curvature_joint_contMDiff F c hc)).contDiffOn
  have htime (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      HasDerivAt (fun s => e (c x s)) (H t x) t :=
    (c2ShrinkingCurve_embedded_interior_equation (m63C2_of_m62 hc) he).2 t
      (by simpa only [interior_Icc] using ht) x
  have hper (t : ℝ) (ht : t ∈ Ioo a b) : Function.Periodic (H t) curvePeriod := by
    intro x
    have heq : (fun s => e (c (x + curvePeriod) s)) =ᶠ[𝓝 t] (fun s => e (c x s)) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      rw [hc.periodic s (Ioo_subset_Icc_self hs) x]
    exact ((htime t ht (x + curvePeriod)).congr_of_eventuallyEq heq.symm).unique
      (htime t ht x)
  refine ⟨?_, hclosed, hsmooth⟩
  intro t ht x
  have heq : EqOn (fun s => H s (x + curvePeriod)) (fun s => H s x) (Ioo a b) :=
    fun s hs => hper s hs x
  exact heq.of_subset_closure
    (hclosed.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨mem_univ _, hs⟩))
    (hclosed.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨mem_univ _, hs⟩))
    Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne]) ht

theorem exists_periodic_embeddedCurvature_restart_data
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M) (hab : a < b)
    (hc : M62ShrinkingCurve F c) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e) :
    let H : ℝ → ℝ → W := fun t x =>
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x)
    ∃ h h₁ h₂ hdot : ℝ → C(AddCircle curvePeriod, W),
      ContinuousOn h (Icc a b) ∧ ContinuousOn h₁ (Ioo a b) ∧
      ContinuousOn h₂ (Ioo a b) ∧ ContinuousOn hdot (Ioo a b) ∧
      (∀ t ∈ Icc a b, ∀ x : ℝ, h t (x : AddCircle curvePeriod) = H t x) ∧
      (∀ t ∈ Ioo a b, ∀ x : ℝ, h₁ t (x : AddCircle curvePeriod) = deriv (H t) x) ∧
      (∀ t ∈ Ioo a b, ∀ x : ℝ,
        h₂ t (x : AddCircle curvePeriod) = iteratedDeriv 2 (H t) x) ∧
      (∀ t ∈ Ioo a b, ∀ x : ℝ,
        hdot t (x : AddCircle curvePeriod) = deriv (fun r => H r x) t) ∧
      (∀ t ∈ Ioo a b, ∀ x : ℝ,
        HasDerivAt (fun y : ℝ => h t (y : AddCircle curvePeriod))
          (h₁ t (x : AddCircle curvePeriod)) x) ∧
      (∀ t ∈ Ioo a b, ∀ x : ℝ,
        HasDerivAt (fun y : ℝ => h₁ t (y : AddCircle curvePeriod))
          (h₂ t (x : AddCircle curvePeriod)) x) ∧
      (∀ t ∈ Ioo a b, ∀ x : ℝ,
        HasDerivAt (fun r => h r (x : AddCircle curvePeriod))
          (hdot t (x : AddCircle curvePeriod)) t) := by
  classical
  dsimp only
  let H : ℝ × ℝ → W := fun z =>
    mfderiv (𝓡 n) 𝓘(ℝ, W) e (c z.1 z.2) (m62CurvatureVector F c z.2 z.1)
  let X := M08.coordinatePartialS H
  let XX := M08.coordinatePartialS X
  let T := M08.coordinatePartialU H
  let Ω : Set (ℝ × ℝ) := univ ×ˢ Ioo a b
  have hΩ : IsOpen Ω := isOpen_univ.prod isOpen_Ioo
  obtain ⟨hper, hclosed, hsmooth⟩ := embeddedCurvature_closed_periodic_data F c hab hc he
  change ContinuousOn H (univ ×ˢ Icc a b) at hclosed
  change ContDiffOn ℝ ∞ H Ω at hsmooth
  have hX : ContDiffOn ℝ ∞ X Ω := M08.coordinatePartialS_contDiffOn hΩ H hsmooth
  have hXX : ContDiffOn ℝ ∞ XX Ω := M08.coordinatePartialS_contDiffOn hΩ X hX
  have hT : ContDiffOn ℝ ∞ T Ω := M08.coordinatePartialU_contDiffOn hΩ H hsmooth
  have hdspace (f : ℝ × ℝ → W) (hf : ContDiffOn ℝ ∞ f Ω)
      (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      HasDerivAt (fun y => f (y, t)) (M08.coordinatePartialS f (x, t)) x := by
    have hd : DifferentiableAt ℝ f (x, t) :=
      (hf.contDiffAt (hΩ.mem_nhds ⟨mem_univ _, ht⟩)).differentiableAt (by simp)
    exact M08.coordinateSlice_fst_hasDerivAt f hd
  have hdtime (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      HasDerivAt (fun r => H (x, r)) (T (x, t)) t := by
    have hd : DifferentiableAt ℝ H (x, t) :=
      (hsmooth.contDiffAt (hΩ.mem_nhds ⟨mem_univ _, ht⟩)).differentiableAt (by simp)
    exact M08.coordinateSlice_snd_hasDerivAt H hd
  have hXeq (t : ℝ) (ht : t ∈ Ioo a b) :
      (fun x => X (x, t)) = deriv (fun x => H (x, t)) :=
    funext fun x => (hdspace H hsmooth t ht x).deriv.symm
  have hXXeq (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      XX (x, t) = iteratedDeriv 2 (fun y => H (y, t)) x := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, ← hXeq t ht]
    exact (hdspace X hX t ht x).deriv.symm
  have hderivper {f : ℝ → W} (hp : Function.Periodic f curvePeriod) :
      Function.Periodic (deriv f) curvePeriod := by
    intro x
    rw [← deriv_comp_add_const]
    exact congrArg (fun g : ℝ → W => deriv g x) (funext hp)
  have hXper (t : ℝ) (ht : t ∈ Ioo a b) :
      Function.Periodic (fun x => X (x, t)) curvePeriod := by
    rw [hXeq t ht]
    exact hderivper (hper t (Ioo_subset_Icc_self ht))
  have hXXper (t : ℝ) (ht : t ∈ Ioo a b) :
      Function.Periodic (fun x => XX (x, t)) curvePeriod := by
    have heq : (fun x => XX (x, t)) = deriv (fun x => X (x, t)) :=
      funext fun x => (hdspace X hX t ht x).deriv.symm
    rw [heq]
    exact hderivper (hXper t ht)
  have hTper (t : ℝ) (ht : t ∈ Ioo a b) :
      Function.Periodic (fun x => T (x, t)) curvePeriod := by
    intro x
    have heq : (fun r => H (x + curvePeriod, r)) =ᶠ[𝓝 t] (fun r => H (x, r)) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
      exact hper r (Ioo_subset_Icc_self hr) x
    exact ((hdtime t ht (x + curvePeriod)).congr_of_eventuallyEq heq.symm).unique
      (hdtime t ht x)
  have descend (J : Set ℝ) (f : ℝ × ℝ → W)
      (hf : ContinuousOn f (univ ×ˢ J))
      (hp : ∀ t ∈ J, Function.Periodic (fun x => f (x, t)) curvePeriod) :
      ∃ g : ℝ → C(AddCircle curvePeriod, W), ContinuousOn g J ∧
        ∀ t ∈ J, ∀ x : ℝ, g t (x : AddCircle curvePeriod) = f (x, t) := by
    let g : ℝ → C(AddCircle curvePeriod, W) := fun t => if ht : t ∈ J then
      ⟨(hp t ht).lift,
        (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples curvePeriod)).continuous_iff.mpr
          (hf.comp_continuous (continuous_id.prodMk continuous_const)
            (fun x => ⟨mem_univ _, ht⟩))⟩ else 0
    have hg (t : ℝ) (ht : t ∈ J) (x : ℝ) :
        g t (x : AddCircle curvePeriod) = f (x, t) := by
      simp only [g, dif_pos ht, ContinuousMap.coe_mk, Function.Periodic.lift_coe]
    refine ⟨g, continuousOn_iff_continuous_domRestrict.mpr ?_, hg⟩
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hquot : IsOpenQuotientMap
        (fun p : J × ℝ => (p.1, (p.2 : AddCircle curvePeriod))) :=
      IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk
    apply hquot.continuous_comp_iff.mp
    have hcomp : Continuous (fun p : J × ℝ => f (p.2, p.1.1)) :=
      hf.comp_continuous (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
        (fun p => ⟨mem_univ _, p.1.2⟩)
    exact hcomp.congr (fun p => (hg p.1.1 p.1.2 p.2).symm)
  obtain ⟨h, hh, hval⟩ := descend (Icc a b) H hclosed hper
  obtain ⟨h₁, hh₁, h₁val⟩ := descend (Ioo a b) X hX.continuousOn hXper
  obtain ⟨h₂, hh₂, h₂val⟩ := descend (Ioo a b) XX hXX.continuousOn hXXper
  obtain ⟨hdot, hhdot, hdotval⟩ := descend (Ioo a b) T hT.continuousOn hTper
  refine ⟨h, h₁, h₂, hdot, hh, hh₁, hh₂, hhdot, hval, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht x
    exact (h₁val t ht x).trans (congrFun (hXeq t ht) x)
  · intro t ht x
    exact (h₂val t ht x).trans (hXXeq t ht x)
  · intro t ht x
    exact (hdotval t ht x).trans (hdtime t ht x).deriv.symm
  · intro t ht x
    rw [h₁val t ht x]
    exact (hdspace H hsmooth t ht x).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (hval t (Ioo_subset_Icc_self ht)))
  · intro t ht x
    rw [h₂val t ht x]
    exact (hdspace X hX t ht x).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (h₁val t ht))
  · intro t ht x
    rw [hdotval t ht x]
    apply (hdtime t ht x).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact hval r (Ioo_subset_Icc_self hr) x

end PoincareConjecture.M63
