import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Matching
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.UpperLevel.Circle
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Caps.Disks
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Level.Disks
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.ArcPairs.CircleExtension
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.UniversalProperty
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Calculus.SupportedRadialSlide
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.CutCircles
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.ResolutionCircles
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Arcs
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Matching.Restriction
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Lift.Cutoff
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Interval.RelativeLocal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.ArcPairs.Support
import PoincareConjecture.Proofs.Horizon.Topology.Connected.IntervalNeighborhoods
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Euclidean.Triangular
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.LocalExtension
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Calculus.RadialExtension
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Caps.Critical
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Coordinates.Critical
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Morse.SignedSquares
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Strips.Family
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.CompactFiber
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Strips
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Strips.Projection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.Reparametrization.Lift
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.CompactCutoff
import Mathlib.Topology.Order.IntermediateValue

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle hiding
  height height_apply height_contMDiff shear shear_image_sphere
open _root_.Poincare.Manifold.Schoenflies.Saddle.Nested
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private theorem common_neighborhood_of_open_patches
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    {f g : X → Y} (hf : Continuous f) (hg : Continuous g)
    (hfi : Injective f) (hgi : Injective g)
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B)
    (hmatch : f '' A = g '' B) :
    ∃ U : Set Y, IsOpen U ∧ f '' A ⊆ U ∧ range f ∩ U = range g ∩ U := by
  let U := (f '' Aᶜ ∪ g '' Bᶜ)ᶜ
  have hU : IsOpen U :=
    ((hA.isClosed_compl.isCompact.image hf).isClosed.union
      (hB.isClosed_compl.isCompact.image hg).isClosed).isOpen_compl
  refine ⟨U, hU, ?_, ?_⟩
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨b, hb, hba⟩ := hmatch ▸ (show f a ∈ f '' A from ⟨a, ha, rfl⟩)
    rintro (⟨a', ha', haa⟩ | ⟨b', hb', hbb⟩)
    · exact ha' (hfi haa ▸ ha)
    · exact hb' (hgi (hbb.trans hba.symm) ▸ hb)
  · ext y
    constructor
    · rintro ⟨⟨a, rfl⟩, hy⟩
      have ha : a ∈ A := by
        by_contra ha
        exact hy (Or.inl ⟨a, ha, rfl⟩)
      have hm : f a ∈ g '' B := hmatch ▸ (show f a ∈ f '' A from ⟨a, ha, rfl⟩)
      exact ⟨image_subset_range _ _ hm, hy⟩
    · rintro ⟨⟨b, rfl⟩, hy⟩
      have hb : b ∈ B := by
        by_contra hb
        exact hy (Or.inr ⟨b, hb, rfl⟩)
      have hm : g b ∈ f '' A := hmatch.symm ▸ (show g b ∈ g '' B from ⟨b, hb, rfl⟩)
      exact ⟨image_subset_range _ _ hm, hy⟩

theorem exists_common_neighborhood_of_matching
    {f : S2 → E3} (hf : Continuous f) (hfi : Injective f)
    {e d : OpenPartialHomeomorph E2 S2}
    (F D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    {s ρ r : Real} (hs : 0 < s) (hr : 0 ≤ r)
    (hrρ : 2 * r < Real.sqrt s * ρ)
    (hd : closedBall (0 : E2) ρ ⊆ d.source)
    (he : ∀ x ∈ closedBall (0 : E2) ρ, Real.sqrt s • x ∈ e.source)
    (hmatch : ∀ x ∈ closedBall (0 : E2) ρ,
      F (d x) = f (e (Real.sqrt s • x))) :
    ∃ U : Set E3, IsOpen U ∧
      (fun x => D (f (e x))) '' SaddleLevel.closedSquare r ⊆ U ∧
      (D '' range f) ∩ U = ((F.trans D) '' sphere (0 : E3) 1) ∩ U := by
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  let L : E2 ≃L[Real] E2 :=
    (LinearEquiv.smulOfNeZero Real E2 (Real.sqrt s) hsqrt.ne').toContinuousLinearEquiv
  let A : Set S2 := e '' (L '' ball (0 : E2) ρ)
  let B : Set S2 := d '' ball (0 : E2) ρ
  have hA : IsOpen A := e.isOpen_image_of_subset_source
    (L.toHomeomorph.isOpenMap _ isOpen_ball) (by
      rintro _ ⟨x, hx, rfl⟩
      exact he x (ball_subset_closedBall hx))
  have hB : IsOpen B := d.isOpen_image_of_subset_source isOpen_ball
    (ball_subset_closedBall.trans hd)
  let f' : S2 → E3 := fun q => D (f q)
  let g' : S2 → E3 := fun q => D (F q)
  have hpatch : f' '' A = g' '' B := by
    ext y
    constructor
    · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
      exact ⟨d x, ⟨x, hx, rfl⟩,
        congrArg D (hmatch x (ball_subset_closedBall hx))⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨e (L x), ⟨L x, ⟨x, hx, rfl⟩, rfl⟩,
        (congrArg D (hmatch x (ball_subset_closedBall hx))).symm⟩
  obtain ⟨U, hU, hAU, hlocal⟩ := common_neighborhood_of_open_patches
    (D.continuous.comp hf) (D.continuous.comp (F.continuous.comp continuous_subtype_val))
    (D.injective.comp hfi) (D.injective.comp (F.injective.comp Subtype.val_injective))
    hA hB hpatch
  refine ⟨U, hU, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxnorm : ‖x‖ ≤ 2 * r := mem_closedBall_zero_iff.mp
      (SaddleLevel.closedSquare_subset_closedBall hr hx)
    have hscaled : (Real.sqrt s)⁻¹ • x ∈ ball (0 : E2) ρ := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hsqrt), inv_mul_eq_div]
      exact (div_lt_iff₀ hsqrt).mpr (by nlinarith)
    have hcancel : L ((Real.sqrt s)⁻¹ • x) = x := by
      change Real.sqrt s • ((Real.sqrt s)⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ hsqrt.ne', one_smul]
    exact hAU ⟨e x, ⟨x, ⟨_, hscaled, hcancel⟩, rfl⟩, rfl⟩
  · have hfr : range f' = D '' range f := by
      simp only [f', ← Function.comp_def, range_comp]
    have hgr : range g' = (F.trans D) '' sphere (0 : E3) 1 := by
      ext y
      constructor
      · rintro ⟨q, rfl⟩
        exact ⟨q, q.property, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨⟨q, hq⟩, rfl⟩
    change range f' ∩ U = range g' ∩ U at hlocal
    rwa [hfr, hgr] at hlocal

theorem flattened_sphere_eq
    (T D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) :
    D '' (T '' (shear (3/10) '' sphere (0 : E3) 1)) =
      {y | polynomial (3/10) (T.symm (D.symm y)) = 1} := by
  rw [shear_image_sphere]
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨D.symm y, ⟨T.symm (D.symm y), hy, T.apply_symm_apply _⟩,
      D.apply_symm_apply _⟩

theorem flattened_level_eq
    (T D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (t : Real) :
    (D '' (T '' (shear (3/10) '' sphere (0 : E3) 1))) ∩ {y | y 2 = t} =
      slice {x | polynomial (3/10) (T.symm (D.symm (toE3 x t))) = 1} t := by
  rw [flattened_sphere_eq]
  ext y
  change (_ = 1 ∧ y 2 = t) ↔ (_ = 1 ∧ y 2 = t)
  have hy : toE3 (toE2 y) (y 2) = y := by
    ext i
    fin_cases i <;> rfl
  constructor <;> rintro ⟨hp, ht⟩ <;> refine ⟨?_, ht⟩
  · simpa only [← ht, hy] using hp
  · simpa only [← ht, hy] using hp

theorem flattened_exterior_level_eq
    (T D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (t : Real) (P : Set E3) :
    ((D '' (T '' (shear (3/10) '' sphere (0 : E3) 1))) ∩ {y | y 2 = t}) \ P =
      slice {x | polynomial (3/10) (T.symm (D.symm (toE3 x t))) = 1 ∧
        toE3 x t ∉ P} t := by
  rw [flattened_sphere_eq]
  ext y
  change ((_ = 1 ∧ y 2 = t) ∧ y ∉ P) ↔ ((_ = 1 ∧ _ ∉ P) ∧ y 2 = t)
  have hy : toE3 (toE2 y) (y 2) = y := by
    ext i
    fin_cases i <;> rfl
  constructor
  · rintro ⟨⟨hp, ht⟩, hn⟩
    simpa only [← ht, hy] using And.intro (And.intro hp hn) ht
  · rintro ⟨⟨hp, hn⟩, ht⟩
    simpa only [← ht, hy] using And.intro (And.intro hp ht) hn

private theorem exists_disjoint_interval_trace_neighborhoods
    {I X : Type*} [Finite I] [TopologicalSpace X] [T2Space X]
    (mu : I → ℝ × ℝ → X) (a b : I → ℝ) (hab : ∀ i, a i ≤ b i)
    (W : I → Set (ℝ × ℝ)) (hW : ∀ i, IsOpen (W i))
    (hmu : ∀ i, ContinuousOn (mu i) (W i))
    (hcentral : ∀ i, ({0} : Set ℝ) ×ˢ Icc (a i) (b i) ⊆ W i)
    (hdisj : Pairwise (fun i j =>
      Disjoint (mu i '' (({0} : Set ℝ) ×ˢ Icc (a i) (b i)))
        (mu j '' (({0} : Set ℝ) ×ˢ Icc (a j) (b j)))))
    {K : Set X} (hK : IsClosed K)
    (havoid : ∀ i s, s ∈ Icc (a i) (b i) → mu i (0, s) ∉ K) :
    ∃ d : ℝ, 0 < d ∧ ∃ U : I → Set X,
      (∀ i, IsOpen (U i) ∧ Disjoint (U i) K ∧
        mu i '' (({0} : Set ℝ) ×ˢ Icc (a i) (b i)) ⊆ U i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      ∀ i, Icc (-d) d ×ˢ Icc (a i - d) (b i + d) ⊆ W i ∧
        mu i '' (Icc (-d) d ×ˢ Icc (a i - d) (b i + d)) ⊆ U i := by
  let F : I → ℝ × ℝ → X := fun i z => mu i z.swap
  let V : I → Set (ℝ × ℝ) := fun i => Prod.swap ⁻¹' W i
  have hV (i : I) : IsOpen (V i) := (hW i).preimage continuous_swap
  have hF (i : I) : ContinuousOn (F i) (V i) :=
    (hmu i).comp continuous_swap.continuousOn (fun _ hx => hx)
  have hcenter (i : I) : Icc (a i) (b i) ×ˢ ({0} : Set ℝ) ⊆ V i := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    exact hcentral i ⟨ht, hs⟩
  have himage (i : I) (S T : Set ℝ) :
      F i '' (S ×ˢ T) = mu i '' (T ×ˢ S) := by
    ext x
    constructor
    · rintro ⟨⟨s, t⟩, ⟨hs, ht⟩, hx⟩
      exact ⟨(t, s), ⟨ht, hs⟩, hx⟩
    · rintro ⟨⟨t, s⟩, ⟨ht, hs⟩, hx⟩
      exact ⟨(s, t), ⟨hs, ht⟩, hx⟩
  have hFdisj : Pairwise (fun i j =>
      Disjoint (F i '' (Icc (a i) (b i) ×ˢ ({0} : Set ℝ)))
        (F j '' (Icc (a j) (b j) ×ˢ ({0} : Set ℝ)))) := by
    intro i j hij
    simpa only [himage] using hdisj hij
  have hFO (i : I) : F i '' (Icc (a i) (b i) ×ˢ ({0} : Set ℝ)) ⊆ Kᶜ := by
    rw [himage]
    rintro x ⟨⟨t, s⟩, ⟨ht, hs⟩, rfl⟩
    have ht0 : t = 0 := ht
    subst t
    exact havoid i s hs
  obtain ⟨d, hd, U, hU, hUdisj, hrect⟩ :=
    Poincare.Topology.exists_disjoint_closed_interval_rectangles F a b hab V hV hF hcenter
      hFdisj (fun _ => Kᶜ) (fun _ => hK.isOpen_compl) hFO
  refine ⟨d, hd, U, ?_, hUdisj, ?_⟩
  · intro i
    refine ⟨(hU i).1, disjoint_left.mpr (fun x hx hxK => (hU i).2.1 hx hxK), ?_⟩
    simpa only [himage] using (hU i).2.2
  · intro i
    refine ⟨?_, ?_⟩
    · rintro ⟨t, s⟩ ⟨ht, hs⟩
      exact (hrect i).1 (show (s, t) ∈
        Icc (a i - d) (b i + d) ×ˢ Icc (-d) d from ⟨hs, ht⟩)
    · simpa only [himage] using (hrect i).2

theorem exists_relative_extension_of_central_arc_pair
    {eta : Real} (heta : 0 < eta)
    (l l₀ l₁ u₁ u₀ u : Fin 2 → Real)
    (hll₀ : ∀ i, l i ≤ l₀ i) (hl₀l₁ : ∀ i, l₀ i < l₁ i)
    (hl₁u₁ : ∀ i, l₁ i ≤ u₁ i) (hu₁u₀ : ∀ i, u₁ i < u₀ i)
    (hu₀u : ∀ i, u₀ i ≤ u i)
    (mu : Fin 2 → Real × Real → E2)
    (W : Fin 2 → Set (Real × Real)) (hW : ∀ i, IsOpen (W i))
    (hrect : ∀ i, Icc (-eta) eta ×ˢ Icc (l i) (u i) ⊆ W i)
    (hmu : ∀ i, ContDiffOn Real ∞ (mu i) (W i))
    (hinj : ∀ i t, t ∈ Icc (-eta) eta →
      InjOn (fun s => mu i (t, s)) (Icc (l i) (u i)))
    (hder : ∀ i t, t ∈ Icc (-eta) eta → ∀ s ∈ Icc (l i) (u i),
      deriv (fun y => mu i (t, y)) s ≠ 0)
    (hstationary : ∀ i t, t ∈ Icc (-eta) eta →
      ∀ s ∈ Icc (l i) (l₁ i) ∪ Icc (u₁ i) (u i),
        mu i (t, s) = mu i (0, s))
    (hdisj : Pairwise (fun i j =>
      Disjoint (mu i '' (({0} : Set Real) ×ˢ Icc (l i) (u i)))
        (mu j '' (({0} : Set Real) ×ˢ Icc (l j) (u j)))))
    (C : Set E2) (hC : IsClosed C)
    (havoid : ∀ i s, s ∈ Icc (l₁ i) (u₁ i) → mu i (0, s) ∉ C) :
    ∃ delta : Real, 0 < delta ∧ delta ≤ eta ∧
      ∃ K O : Set E2, IsCompact K ∧ IsOpen O ∧ C ⊆ O ∧ Disjoint K O ∧
        ∃ Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          (∀ x, Phi 0 x = x) ∧
          ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) ∧
          ContDiff Real ∞ (fun z : Real × E2 => (Phi z.1).symm z.2) ∧
          (∀ t x, x ∉ K → Phi t x = x) ∧
          (∀ t x, x ∈ O → Phi t x = x) ∧
          ∀ i t, t ∈ Icc (-delta) delta → ∀ s ∈ Icc (l i) (u i),
            Phi t (mu i (0, s)) = mu i (t, s) := by
  have hzero : (0 : Real) ∈ Icc (-eta) eta := ⟨by linarith, heta.le⟩
  have hmid (i : Fin 2) : Icc (l₁ i) (u₁ i) ⊆ Icc (l i) (u i) :=
    Icc_subset_Icc ((hll₀ i).trans (hl₀l₁ i).le) ((hu₁u₀ i).le.trans (hu₀u i))
  have hlu (i : Fin 2) : l i ≤ u i :=
    (hll₀ i).trans ((hl₀l₁ i).le.trans
      ((hl₁u₁ i).trans ((hu₁u₀ i).le.trans (hu₀u i))))
  have hcentral (i : Fin 2) : ({0} : Set Real) ×ˢ Icc (l i) (u i) ⊆ W i := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have ht0 : t = 0 := ht
    subst t
    exact hrect i ⟨hzero, hs⟩
  obtain ⟨d, hd, U, hU, hUdisj, hfull⟩ :=
    exists_disjoint_interval_trace_neighborhoods mu l u hlu W hW
      (fun i => (hmu i).continuousOn) hcentral hdisj isClosed_empty
      (fun _ _ _ => notMem_empty _)
  have hcentralMid (i : Fin 2) : ({0} : Set Real) ×ˢ Icc (l₁ i) (u₁ i) ⊆ W i :=
    (prod_mono Subset.rfl (hmid i)).trans (hcentral i)
  have hdisjMid : Pairwise (fun i j =>
      Disjoint (mu i '' (({0} : Set Real) ×ˢ Icc (l₁ i) (u₁ i)))
        (mu j '' (({0} : Set Real) ×ˢ Icc (l₁ j) (u₁ j)))) := by
    intro i j hij
    exact (hdisj hij).mono
      (image_mono (prod_mono Subset.rfl (hmid i)))
      (image_mono (prod_mono Subset.rfl (hmid j)))
  obtain ⟨d', hd', V, hV, _, hmiddle⟩ :=
    exists_disjoint_interval_trace_neighborhoods mu l₁ u₁ hl₁u₁ W hW
      (fun i => (hmu i).continuousOn) hcentralMid hdisjMid hC havoid
  let delta := min eta (min d d')
  have hdelta : 0 < delta := lt_min heta (lt_min hd hd')
  have hdelta_eta : delta ≤ eta := min_le_left _ _
  have hdelta_d : delta ≤ d := (min_le_right _ _).trans (min_le_left _ _)
  have hdelta_d' : delta ≤ d' := (min_le_right _ _).trans (min_le_right _ _)
  have htime {t : Real} (ht : t ∈ Icc (-delta) delta) : t ∈ Icc (-eta) eta :=
    ⟨by linarith [ht.1], ht.2.trans hdelta_eta⟩
  have hbase : -delta ∈ Icc (-delta) delta := ⟨le_rfl, by linarith⟩
  have hcenter : (0 : Real) ∈ Icc (-delta) delta := ⟨by linarith, hdelta.le⟩
  have hwhole (i : Fin 2) (t : Real) (ht : t ∈ Icc (-delta) delta)
      (s : Real) (hs : s ∈ Icc (l i) (u i)) : mu i (t, s) ∈ U i := by
    apply (hfull i).2
    refine ⟨(t, s), ?_, rfl⟩
    exact ⟨⟨by linarith [ht.1], ht.2.trans hdelta_d⟩,
      ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩
  have htrace (i : Fin 2) (t : Real) (ht : t ∈ Icc (-delta) delta)
      (s : Real) (hs : s ∈ Icc (l₁ i) (u₁ i)) : mu i (t, s) ∈ U i ∩ V i := by
    refine ⟨hwhole i t ht s (hmid i hs), ?_⟩
    apply (hmiddle i).2
    refine ⟨(t, s), ?_, rfl⟩
    exact ⟨⟨by linarith [ht.1], ht.2.trans hdelta_d'⟩,
      ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩
  choose K O hK hKU hO hendsO hKO Psi hPsiBase hPsi hPsiFix hPsiFixO hPsiMotion using
    fun i : Fin 2 => exists_relative_ambient_isotopy_of_interval_isotopy_within_of_contDiffOn
      (a := -delta) (b := delta) (by linarith) (hll₀ i) (hl₀l₁ i) (hl₁u₁ i)
      (hu₁u₀ i) (hu₀u i) ((hU i).1.inter (hV i).1) (mu i) (hW i)
      (fun z hz => hrect i ⟨htime hz.1, hz.2⟩) (hmu i)
      (fun t ht => hinj i t (htime ht)) (fun t ht => hder i t (htime ht))
      (fun t ht s hs => (hstationary i t (htime ht) s hs).trans
        (hstationary i (-delta) (htime hbase) s hs).symm) (htrace i)
  let Omega : Fin 2 → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
    fun i t => (Psi i 0).symm.trans (Psi i t)
  have hOmega (i : Fin 2) : ContDiff Real ∞ (fun z : Real × E2 => Omega i z.1 z.2) :=
    (hPsi i).comp (contDiff_fst.prodMk
      ((Psi i 0).symm.contMDiff.contDiff.comp contDiff_snd))
  have hOmegaZero (i : Fin 2) (x : E2) : Omega i 0 x = x :=
    (Psi i 0).apply_symm_apply x
  have hOmegaFix (i : Fin 2) (t : Real) (x : E2) (hx : x ∉ K i) : Omega i t x = x := by
    have hfixInv : (Psi i 0).symm x = x := by
      apply (Psi i 0).injective
      exact ((Psi i 0).apply_symm_apply x).trans (hPsiFix i 0 x hx).symm
    change Psi i t ((Psi i 0).symm x) = x
    rw [hfixInv, hPsiFix i t x hx]
  have hOmegaMotion (i : Fin 2) (t : Real) (ht : t ∈ Icc (-delta) delta)
      (s : Real) (hs : s ∈ Icc (l i) (u i)) :
      Omega i t (mu i (0, s)) = mu i (t, s) := by
    change Psi i t ((Psi i 0).symm (mu i (0, s))) = mu i (t, s)
    rw [← hPsiMotion i 0 hcenter s hs, (Psi i 0).symm_apply_apply]
    exact hPsiMotion i t ht s hs
  let Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
    fun t => (Omega 1 t).trans (Omega 0 t)
  have hPhi : ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) :=
    (hOmega 0).comp (contDiff_fst.prodMk (hOmega 1))
  have hU01 : Disjoint (U 0) (U 1) := hUdisj (by decide : (0 : Fin 2) ≠ 1)
  have hPhiFix (t : Real) (x : E2) (hx : x ∉ K 0 ∪ K 1) : Phi t x = x := by
    change Omega 0 t (Omega 1 t x) = x
    rw [hOmegaFix 1 t x (fun h => hx (Or.inr h)),
      hOmegaFix 0 t x (fun h => hx (Or.inl h))]
  refine ⟨delta, hdelta, hdelta_eta, K 0 ∪ K 1, (K 0 ∪ K 1)ᶜ,
    (hK 0).union (hK 1), ((hK 0).union (hK 1)).isClosed.isOpen_compl,
    ?_, disjoint_compl_right, Phi, ?_, hPhi,
    Plane.Isotopy.ArcPairs.contDiff_family_symm Phi hPhi, hPhiFix, hPhiFix, ?_⟩
  · intro x hx
    rintro (hxK | hxK)
    · exact disjoint_left.mp (hV 0).2.1 (hKU 0 hxK).2 hx
    · exact disjoint_left.mp (hV 1).2.1 (hKU 1 hxK).2 hx
  · intro x
    change Omega 0 0 (Omega 1 0 x) = x
    rw [hOmegaZero, hOmegaZero]
  · intro i t ht s hs
    fin_cases i
    · change Omega 0 t (Omega 1 t (mu 0 (0, s))) = mu 0 (t, s)
      rw [hOmegaFix 1 t _ (fun hx => disjoint_left.mp hU01
        (hwhole 0 0 hcenter s hs) (hKU 1 hx).1)]
      exact hOmegaMotion 0 t ht s hs
    · change Omega 0 t (Omega 1 t (mu 1 (0, s))) = mu 1 (t, s)
      rw [hOmegaMotion 1 t ht s hs]
      exact hOmegaFix 0 t _ (fun hx => disjoint_left.mp hU01 (hKU 0 hx).1
        (hwhole 1 t ht s hs))

section ExteriorRestriction

variable {X : Type*} [TopologicalSpace X]

private theorem image_labeled_pair_of_union_image
    (Q : X ≃ₜ X) (A B : Fin 2 → Set X)
    (hA : ∀ i, IsPreconnected (A i))
    (hB : ∀ i, IsClosed (B i))
    (hdisj : Disjoint (B 0) (B 1))
    (hunion : Q '' (A 0 ∪ A 1) = B 0 ∪ B 1)
    (hlabel : ∀ i, ∃ x ∈ A i, Q x ∈ B i) :
    ∀ i, Q '' A i = B i := by
  have hsub (i : Fin 2) : Q '' A i ⊆ B i := by
    have hcover : Q '' A i ⊆ B 0 ∪ B 1 := by
      rw [← hunion]
      apply image_mono
      fin_cases i
      · exact subset_union_left
      · exact subset_union_right
    have hconn := (hA i).image Q Q.continuous.continuousOn
    have hside := isPreconnected_iff_subset_of_disjoint_closed.mp hconn
      (B 0) (B 1) (hB 0) (hB 1) hcover (by
        rw [hdisj.inter_eq, inter_empty])
    obtain ⟨x, hx, hxB⟩ := hlabel i
    fin_cases i
    · rcases hside with h | h
      · exact h
      · exact False.elim (disjoint_left.mp hdisj hxB (h (mem_image_of_mem Q hx)))
    · rcases hside with h | h
      · exact False.elim (disjoint_left.mp hdisj (h (mem_image_of_mem Q hx)) hxB)
      · exact h
  intro i
  apply Subset.antisymm (hsub i)
  intro y hy
  have hyU : y ∈ Q '' (A 0 ∪ A 1) := by
    rw [hunion]
    fin_cases i
    · exact Or.inl hy
    · exact Or.inr hy
  obtain ⟨x, hx, rfl⟩ := hyU
  fin_cases i
  · rcases hx with hx | hx
    · exact mem_image_of_mem Q hx
    · exact False.elim (disjoint_left.mp hdisj hy (hsub 1 (mem_image_of_mem Q hx)))
  · rcases hx with hx | hx
    · exact False.elim (disjoint_left.mp hdisj (hsub 0 (mem_image_of_mem Q hx)) hy)
    · exact mem_image_of_mem Q hx

private theorem image_labeled_exterior_pair
    (Q : X ≃ₜ X) (L L' C O : Set X) (A B : Fin 2 → Set X)
    (hOC : O ⊆ C) (hfix : EqOn Q id C)
    (hlevel : Q '' L = L')
    (hsource : L \ O = A 0 ∪ A 1)
    (htarget : L' \ O = B 0 ∪ B 1)
    (hA : ∀ i, IsPreconnected (A i))
    (hB : ∀ i, IsClosed (B i))
    (hdisj : Disjoint (B 0) (B 1))
    (p : Fin 2 → X)
    (hpC : ∀ i, p i ∈ C) (hpA : ∀ i, p i ∈ A i) (hpB : ∀ i, p i ∈ B i) :
    ∀ i, Q '' A i = B i := by
  have hO : Q '' O = O := (hfix.mono hOC).image_eq.trans (image_id _)
  apply image_labeled_pair_of_union_image Q A B hA hB hdisj
  · rw [← hsource, image_sdiff Q.injective, hlevel, hO, htarget]
  · intro i
    exact ⟨p i, hpA i, (hfix (hpC i)).symm ▸ hpB i⟩

theorem image_labeled_exterior_arcs [T2Space X]
    (Q : X ≃ₜ X) (L L' C O : Set X)
    (hOC : O ⊆ C) (hfix : EqOn Q id C) (hlevel : Q '' L = L')
    (γ μ : Fin 2 → Real → X) (a b c d : Fin 2 → Real)
    (hab : ∀ i, a i ≤ b i) (hcd : ∀ i, c i ≤ d i)
    (hγ : ∀ i, ContinuousOn (γ i) (Icc (a i) (b i)))
    (hμ : ∀ i, ContinuousOn (μ i) (Icc (c i) (d i)))
    (hsource : L \ O = γ 0 '' Icc (a 0) (b 0) ∪ γ 1 '' Icc (a 1) (b 1))
    (htarget : L' \ O = μ 0 '' Icc (c 0) (d 0) ∪ μ 1 '' Icc (c 1) (d 1))
    (hdisj : Disjoint (μ 0 '' Icc (c 0) (d 0)) (μ 1 '' Icc (c 1) (d 1)))
    (hends : ∀ i, γ i (a i) = μ i (c i))
    (hendsC : ∀ i, γ i (a i) ∈ C) :
    ∀ i, Q '' (γ i '' Icc (a i) (b i)) = μ i '' Icc (c i) (d i) := by
  exact image_labeled_exterior_pair Q L L' C O
    (fun i => γ i '' Icc (a i) (b i)) (fun i => μ i '' Icc (c i) (d i))
    hOC hfix hlevel hsource htarget
    (fun i => isPreconnected_Icc.image (γ i) (hγ i))
    (fun i => (isCompact_Icc.image_of_continuousOn (hμ i)).isClosed) hdisj
    (fun i => γ i (a i)) hendsC
    (fun i => mem_image_of_mem _ ⟨le_rfl, hab i⟩)
    (fun i => (hends i).symm ▸ mem_image_of_mem (μ i) ⟨le_rfl, hcd i⟩)

end ExteriorRestriction

theorem image_recut_interval_of_endpoint_agreement
    {T X Y : Type*} [LinearOrder T]
    {a a₁ b₁ b A B : T}
    (haA : a ≤ A) (hAa₁ : A ≤ a₁)
    (hb₁B : b₁ ≤ B) (hBb : B ≤ b)
    (gamma : T → X) (mu : T → Y) (Q : X → Y)
    (hgamma : InjOn gamma (Icc a b)) (hmu : InjOn mu (Icc a b))
    (hQ : Injective Q)
    (hfull : Q '' (gamma '' Icc a b) = mu '' Icc a b)
    (hends : ∀ s ∈ Icc a a₁ ∪ Icc b₁ b, Q (gamma s) = mu s) :
    Q '' (gamma '' Icc A B) = mu '' Icc A B := by
  have hsub : Icc A B ⊆ Icc a b := Icc_subset_Icc haA hBb
  have hmem {s t : T} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
      (heq : Q (gamma s) = mu t) : s ∈ Icc A B ↔ t ∈ Icc A B := by
    by_cases hst : s = t
    · exact hst ▸ Iff.rfl
    have hsEnd : s ∉ Icc a a₁ ∪ Icc b₁ b := by
      intro hsEnd
      exact hst (hmu hs ht ((hends s hsEnd).symm.trans heq))
    have htEnd : t ∉ Icc a a₁ ∪ Icc b₁ b := by
      intro htEnd
      exact hst (hgamma hs ht (hQ (heq.trans (hends t htEnd).symm)))
    have hinside (z : T) (hz : z ∈ Icc a b)
        (hend : z ∉ Icc a a₁ ∪ Icc b₁ b) : z ∈ Icc A B := by
      constructor
      · by_contra hAz
        exact hend (Or.inl ⟨hz.1, (lt_of_not_ge hAz).le.trans hAa₁⟩)
      · by_contra hzB
        exact hend (Or.inr ⟨hb₁B.trans (lt_of_not_ge hzB).le, hz.2⟩)
    exact ⟨fun _ => hinside t ht htEnd, fun _ => hinside s hs hsEnd⟩
  apply Subset.antisymm
  · rintro y ⟨x, ⟨s, hs, rfl⟩, rfl⟩
    obtain ⟨t, ht, heq⟩ := hfull.subset
      (show Q (gamma s) ∈ Q '' (gamma '' Icc a b) from
        ⟨gamma s, ⟨s, hsub hs, rfl⟩, rfl⟩)
    exact ⟨t, (hmem (hsub hs) ht heq.symm).mp hs, heq⟩
  · rintro y ⟨t, ht, rfl⟩
    obtain ⟨x, ⟨s, hs, rfl⟩, heq⟩ := hfull.superset
      (show mu t ∈ mu '' Icc a b from ⟨t, hsub ht, rfl⟩)
    exact ⟨gamma s, ⟨s, (hmem hs (hsub ht) heq).mpr ht, rfl⟩, heq⟩

theorem exists_rebased_arc_pair_matching
    (γ : Fin 2 → Real → E2) (μ : Fin 2 → Real × Real → E2)
    (l l₁ u₁ u : Fin 2 → Real) (A B : Fin 2 → Real → Real)
    (horder : ∀ i, l₁ i ≤ u₁ i)
    {I : Set Real} {a : Real} (ha : a ∈ I)
    (hcuts : ∀ i t, t ∈ I →
      l i ≤ A i t ∧ A i t ≤ l₁ i ∧ u₁ i ≤ B i t ∧ B i t ≤ u i)
    (hγ : ∀ i, InjOn (γ i) (Icc (l i) (u i)))
    (hμ : ∀ i t, t ∈ I → InjOn (fun s => μ i (t, s)) (Icc (l i) (u i)))
    (Ψ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hΨ : ContDiff Real ∞ (fun z : Real × E2 => Ψ z.1 z.2))
    (Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {K L C : Set E2} (hK : IsCompact K) (hL : IsCompact L)
    (hKC : Disjoint K C) (hLC : Disjoint L C)
    (hΨfix : ∀ t x, x ∉ K → Ψ t x = x)
    (hQfix : ∀ x, x ∉ L → Q x = x)
    (hmove : ∀ i t, t ∈ I → ∀ s ∈ Icc (l i) (u i),
      Ψ t (μ i (0, s)) = μ i (t, s))
    (hanchor : ∀ i, Q '' (γ i '' Icc (l i) (u i)) =
      (fun s => μ i (a, s)) '' Icc (l i) (u i))
    (hends : ∀ i s, s ∈ Icc (l i) (l₁ i) ∪ Icc (u₁ i) (u i) →
      Q (γ i s) = μ i (a, s)) :
    ∃ S O : Set E2, IsCompact S ∧ IsOpen O ∧ C ⊆ O ∧ Disjoint S O ∧
      ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2) ∧
        (∀ t x, x ∉ S → Φ t x = x) ∧
        (∀ t x, x ∈ O → Φ t x = x) ∧
        ∀ i t, t ∈ I → Φ t '' (γ i '' Icc (A i t) (B i t)) =
          (fun s => μ i (t, s)) '' Icc (A i t) (B i t) := by
  let Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
    fun t => (Q.trans (Ψ a).symm).trans (Ψ t)
  have hΦ : ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) :=
    hΨ.comp (contDiff_fst.prodMk
      (((Q.trans (Ψ a).symm).contMDiff.contDiff).comp contDiff_snd))
  have hΦfix (t : Real) (x : E2) (hx : x ∉ K ∪ L) : Φ t x = x := by
    have hxK : x ∉ K := fun h => hx (Or.inl h)
    have hxL : x ∉ L := fun h => hx (Or.inr h)
    have hinv : (Ψ a).symm x = x := by
      apply (Ψ a).injective
      exact ((Ψ a).apply_symm_apply x).trans (hΨfix a x hxK).symm
    change Ψ t ((Ψ a).symm (Q x)) = x
    rw [hQfix x hxL, hinv, hΨfix t x hxK]
  have hpoint (i : Fin 2) (t : Real) (ht : t ∈ I)
      (s : Real) (hs : s ∈ Icc (l i) (u i))
      (x : E2) (hx : Q x = μ i (a, s)) : Φ t x = μ i (t, s) := by
    change Ψ t ((Ψ a).symm (Q x)) = μ i (t, s)
    rw [hx, ← hmove i a ha s hs, Diffeomorph.symm_apply_apply, hmove i t ht s hs]
  have hfull (i : Fin 2) (t : Real) (ht : t ∈ I) :
      Φ t '' (γ i '' Icc (l i) (u i)) =
        (fun s => μ i (t, s)) '' Icc (l i) (u i) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨s, hs, heq⟩ := (hanchor i).subset (mem_image_of_mem Q hx)
      exact ⟨s, hs, (hpoint i t ht s hs x heq.symm).symm⟩
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨x, hx, heq⟩ := (hanchor i).superset (mem_image_of_mem _ hs)
      exact ⟨x, hx, hpoint i t ht s hs x heq⟩
  refine ⟨K ∪ L, (K ∪ L)ᶜ, hK.union hL, (hK.union hL).isClosed.isOpen_compl,
    ?_, disjoint_compl_right, Φ, hΦ,
    Plane.Isotopy.ArcPairs.contDiff_family_symm Φ hΦ, hΦfix, hΦfix, ?_⟩
  · intro x hx
    rintro (hxK | hxL)
    · exact disjoint_left.mp hKC hxK hx
    · exact disjoint_left.mp hLC hxL hx
  · intro i t ht
    obtain ⟨hlA, hAl, huB, hBu⟩ := hcuts i t ht
    apply image_recut_interval_of_endpoint_agreement hlA hAl huB hBu
      (γ i) (fun s => μ i (t, s)) (Φ t) (hγ i) (hμ i t ht)
      (Φ t).injective (hfull i t ht)
    intro s hs
    have hslu : s ∈ Icc (l i) (u i) := by
      rcases hs with hs | hs
      · exact ⟨hs.1, hs.2.trans ((horder i).trans (huB.trans hBu))⟩
      · exact ⟨(hlA.trans (hAl.trans (horder i))).trans hs.1, hs.2⟩
    exact hpoint i t ht s hslu (γ i s) (hends i s hs)

theorem exists_slab_matching_of_regular_anchor_matches
    {eta : Real} (heta : 0 < eta)
    (l l₀ l₁ u₁ u₀ u : Fin 2 → Real)
    (hll₀ : ∀ i, l i ≤ l₀ i) (hl₀l₁ : ∀ i, l₀ i < l₁ i)
    (hl₁u₁ : ∀ i, l₁ i ≤ u₁ i) (hu₁u₀ : ∀ i, u₁ i < u₀ i)
    (hu₀u : ∀ i, u₀ i ≤ u i)
    (mu : Fin 2 → Real × Real → E2)
    (W : Fin 2 → Set (Real × Real)) (hW : ∀ i, IsOpen (W i))
    (hrect : ∀ i, Icc (-eta) eta ×ˢ Icc (l i) (u i) ⊆ W i)
    (hmu : ∀ i, ContDiffOn Real ∞ (mu i) (W i))
    (hinj : ∀ i t, t ∈ Icc (-eta) eta →
      InjOn (fun s => mu i (t, s)) (Icc (l i) (u i)))
    (hder : ∀ i t, t ∈ Icc (-eta) eta → ∀ s ∈ Icc (l i) (u i),
      deriv (fun y => mu i (t, y)) s ≠ 0)
    (hstationary : ∀ i t, t ∈ Icc (-eta) eta →
      ∀ s ∈ Icc (l i) (l₁ i) ∪ Icc (u₁ i) (u i),
        mu i (t, s) = mu i (0, s))
    (hdisj : Pairwise (fun i j =>
      Disjoint (mu i '' (({0} : Set Real) ×ˢ Icc (l i) (u i)))
        (mu j '' (({0} : Set Real) ×ˢ Icc (l j) (u j)))))
    (C : Set E2) (hC : IsClosed C)
    (havoid : ∀ i s, s ∈ Icc (l₁ i) (u₁ i) → mu i (0, s) ∉ C)
    (gamma : Fin 2 → Real → E2)
    (hgamma : ∀ i, InjOn (gamma i) (Icc (l i) (u i)))
    (A B : Fin 2 → Real → Real)
    (hcuts : ∀ i t, t ∈ Icc (-eta) eta →
      l i ≤ A i t ∧ A i t ≤ l₁ i ∧ u₁ i ≤ B i t ∧ B i t ≤ u i)
    (hregular : ∀ a ∈ Icc (-eta) eta, a ≠ 0 →
      ∃ L : Set E2, IsCompact L ∧ Disjoint L C ∧
        ∃ Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          (∀ x, x ∉ L → Q x = x) ∧
          (∀ i, Q '' (gamma i '' Icc (l i) (u i)) =
            (fun s => mu i (a, s)) '' Icc (l i) (u i)) ∧
          ∀ i s, s ∈ Icc (l i) (l₁ i) ∪ Icc (u₁ i) (u i) →
            Q (gamma i s) = mu i (a, s)) :
    ∃ delta : Real, 0 < delta ∧ delta ≤ eta ∧
      ∃ S O : Set E2, IsCompact S ∧ IsOpen O ∧ C ⊆ O ∧ Disjoint S O ∧
        ∃ Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) ∧
          ContDiff Real ∞ (fun z : Real × E2 => (Phi z.1).symm z.2) ∧
          (∀ t x, x ∉ S → Phi t x = x) ∧
          (∀ t x, x ∈ O → Phi t x = x) ∧
          ∀ i t, t ∈ Icc (-delta) delta →
            Phi t '' (gamma i '' Icc (A i t) (B i t)) =
              (fun s => mu i (t, s)) '' Icc (A i t) (B i t) := by
  obtain ⟨delta, hdelta, hdelta_eta, K, O, hK, _, hCO, hKO,
      Psi, _, hPsi, _, hPsiFix, _, hmove⟩ :=
    exists_relative_extension_of_central_arc_pair heta l l₀ l₁ u₁ u₀ u
      hll₀ hl₀l₁ hl₁u₁ hu₁u₀ hu₀u mu W hW hrect hmu hinj hder
      hstationary hdisj C hC havoid
  have htime {t : Real} (ht : t ∈ Icc (-delta) delta) : t ∈ Icc (-eta) eta :=
    ⟨by linarith [ht.1], ht.2.trans hdelta_eta⟩
  have hanchorTime : delta / 2 ∈ Icc (-delta) delta := ⟨by linarith, by linarith⟩
  obtain ⟨L, hL, hLC, Q, hQfix, hanchor, hends⟩ :=
    hregular (delta / 2) (htime hanchorTime) (by positivity)
  refine ⟨delta, hdelta, hdelta_eta, ?_⟩
  exact exists_rebased_arc_pair_matching gamma mu l l₁ u₁ u A B hl₁u₁ hanchorTime
    (fun i t ht => hcuts i t (htime ht)) hgamma
    (fun i t ht => hinj i t (htime ht)) Psi hPsi Q hK hL
    (hKO.mono_right hCO) hLC hPsiFix hQfix hmove hanchor hends

section EndpointCoordinates

open Filter
open scoped _root_.Topology
set_option backward.isDefEq.respectTransparency false

private theorem exists_small_time_cutoff {ε : Real} (hε : 0 < ε) :
    ∃ r : Real, 0 < r ∧ r < ε ∧ ∃ θ : Real → Real,
      ContDiff Real ∞ θ ∧ (∀ t, θ t ∈ Ioo (-ε) ε) ∧
      ∀ t ∈ Icc (-r) r, θ t = t := by
  let χ : ContDiffBump (0 : Real) :=
    { rIn := ε / 4
      rOut := ε / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  refine ⟨ε / 4, by positivity, by linarith, fun t => χ t * t,
    χ.contDiff.mul contDiff_id, ?_, ?_⟩
  · intro t
    have hbound : |χ t * t| < ε := by
      by_cases ht : |t| < ε / 2
      · rw [abs_mul, abs_of_nonneg χ.nonneg]
        calc
          χ t * |t| ≤ 1 * |t| := mul_le_mul_of_nonneg_right χ.le_one (abs_nonneg _)
          _ < ε := by simpa using ht.trans (by linarith : ε / 2 < ε)
      · have hz : χ t = 0 := χ.zero_of_le_dist (by
          simpa only [Real.dist_eq, sub_zero] using le_of_not_gt ht)
        simpa only [hz, zero_mul, abs_zero] using hε
    exact abs_lt.mp hbound
  · intro t ht
    change χ t * t = t
    rw [χ.one_of_mem_closedBall (by
      simpa only [mem_closedBall, Real.dist_eq, sub_zero] using abs_le.mpr ht), one_mul]

private theorem exists_cutoff_parameter_family
    (α : Real × Real → Real) (hα : ContDiff Real ∞ α)
    (χ : Real → Real) (hχ : ContDiff Real ∞ χ) (hχc : HasCompactSupport χ)
    (hzero : ∀ s ∈ tsupport χ, α (0, s) = s) :
    ∃ r : Real, 0 < r ∧
      ∃ R : Real → Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞,
        (∀ s, R 0 s = s) ∧
        ContDiff Real ∞ (fun z : Real × Real => R z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × Real => (R z.1).symm z.2) ∧
        (∀ t s, s ∉ tsupport χ → R t s = s) ∧
        ∀ t ∈ Icc (-r) r, ∀ s, R t s = s + χ s * (α (t, s) - s) := by
  let F : Real × Real → Real := fun z => z.2 + χ z.2 * (α z - z.2)
  have hF : ContDiff Real ∞ F :=
    contDiff_snd.add ((hχ.comp contDiff_snd).mul (hα.sub contDiff_snd))
  have hFzero : (fun s => F (0, s)) = id := by
    funext s
    by_cases hs : s ∈ tsupport χ
    · simp [F, hzero s hs]
    · simp [F, image_eq_zero_of_notMem_tsupport hs]
  let dF : Real × Real → Real := fun z => deriv (fun s => F (z.1, s)) z.2
  have hdF : ContDiff Real ∞ dF := by
    have hA : ContDiff Real ∞ (fun z : Real × Real =>
        fderiv Real (fun s => F (z.1, s)) z.2) :=
      (hF.comp (contDiff_fst.fst.prodMk contDiff_snd)).fderiv contDiff_snd (by simp)
    exact hA.clm_apply contDiff_const
  have hdFzero (s : Real) : dF (0, s) = 1 := by
    change deriv (fun s => F (0, s)) s = 1
    rw [hFzero, deriv_id]
  have hevent : ∀ᶠ t in 𝓝 (0 : Real), ∀ s ∈ tsupport χ, 0 < dF (t, s) := by
    apply hχc.isCompact.eventually_forall_of_forall_eventually
    intro s hs
    exact hdF.continuous.continuousAt.eventually
      (Ioi_mem_nhds (by rw [hdFzero]; norm_num))
  obtain ⟨ε, hε, hεd⟩ := Metric.mem_nhds_iff.mp hevent
  obtain ⟨r, hr, _, θ, hθ, hθrange, hθid⟩ := exists_small_time_cutoff hε
  let G : Real × Real → Real := fun z => F (θ z.1, z.2)
  have hG : ContDiff Real ∞ G := hF.comp ((hθ.comp contDiff_fst).prodMk contDiff_snd)
  have hGfix (t s : Real) (hs : s ∉ tsupport χ) : G (t, s) = s := by
    simp [G, F, image_eq_zero_of_notMem_tsupport hs]
  have hGder (t s : Real) : 0 < deriv (fun y => G (t, y)) s := by
    by_cases hs : s ∈ tsupport χ
    · apply hεd (show θ t ∈ ball (0 : Real) ε from ?_) s hs
      simpa only [mem_ball, Real.dist_eq, sub_zero] using abs_lt.mpr (hθrange t)
    · have heq : (fun y => G (t, y)) =ᶠ[𝓝 s] id := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hs] with y hy
        exact hGfix t y hy
      rw [heq.deriv_eq, deriv_id]
      norm_num
  have hGbound (t : Real) : ∃ C : Real, ∀ s, |G (t, s) - s| ≤ C := by
    obtain ⟨B, hB⟩ := hχc.isCompact.exists_bound_of_continuousOn
      ((hG.continuous.comp (continuous_const.prodMk continuous_id)).sub continuous_id).continuousOn
    refine ⟨max B 0, ?_⟩
    intro s
    by_cases hs : s ∈ tsupport χ
    · exact (hB s hs).trans (le_max_left _ _)
    · rw [hGfix t s hs, sub_self, abs_zero]
      exact le_max_right _ _
  have hbij (t : Real) : Bijective (fun s => G (t, s)) :=
    Poincare.Manifold.bijective_of_deriv_pos_of_bounded_displacement
      (hG.continuous.comp (continuous_const.prodMk continuous_id)) (hGder t) (hGbound t)
  obtain ⟨g, hg, hright, hleft⟩ :=
    Poincare.Manifold.exists_smooth_scalar_inverse hG hbij (fun t s => (hGder t s).ne')
  let R (t : Real) : Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞ :=
    { toEquiv :=
        { toFun := fun s => G (t, s)
          invFun := fun s => g (t, s)
          left_inv := hleft t
          right_inv := hright t }
      contMDiff_toFun := (hG.comp (contDiff_const.prodMk contDiff_id)).contMDiff
      contMDiff_invFun := (hg.comp (contDiff_const.prodMk contDiff_id)).contMDiff }
  refine ⟨r, hr, R, ?_, hG, hg, hGfix, ?_⟩
  · intro s
    change F (θ 0, s) = s
    rw [hθid 0 ⟨by linarith, hr.le⟩]
    exact congrFun hFzero s
  · intro t ht s
    change F (θ t, s) = _
    rw [hθid t ht]

private theorem exists_cutoff_parameter_family_of_contDiffOn
    (α : Real × Real → Real) {W : Set (Real × Real)} (hW : IsOpen W)
    (χ : Real → Real) (hχ : ContDiff Real ∞ χ) (hχc : HasCompactSupport χ)
    (hWzero : ∀ s ∈ tsupport χ, (0, s) ∈ W)
    (hα : ContDiffOn Real ∞ α W)
    (hzero : ∀ s ∈ tsupport χ, α (0, s) = s) :
    ∃ r : Real, 0 < r ∧
      ∃ R : Real → Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞,
        (∀ s, R 0 s = s) ∧
        ContDiff Real ∞ (fun z : Real × Real => R z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × Real => (R z.1).symm z.2) ∧
        (∀ t s, s ∉ tsupport χ → R t s = s) ∧
        ∀ t ∈ Icc (-r) r, ∀ s, R t s = s + χ s * (α (t, s) - s) := by
  have hK : IsCompact (({0} : Set Real) ×ˢ tsupport χ) :=
    isCompact_singleton.prod hχc.isCompact
  have hKW : ({0} : Set Real) ×ˢ tsupport χ ⊆ W := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    simp only [mem_singleton_iff] at ht
    subst t
    exact hWzero s hs
  obtain ⟨β, hβ, _, hβα⟩ :=
    Poincare.Parabolic.Interior.exists_compact_smooth_extension hK hW hKW hα
  have hβzero (s : Real) (hs : s ∈ tsupport χ) : β (0, s) = s :=
    ((hβα (0, s) ⟨rfl, hs⟩).self_of_nhds).trans (hzero s hs)
  have hevent : ∀ᶠ t in 𝓝 (0 : Real), ∀ s ∈ tsupport χ, β (t, s) = α (t, s) := by
    apply hχc.isCompact.eventually_forall_of_forall_eventually
    intro s hs
    exact hβα (0, s) ⟨rfl, hs⟩
  obtain ⟨ε, hε, hεeq⟩ := Metric.mem_nhds_iff.mp hevent
  obtain ⟨r, hr, R, hRzero, hR, hRinv, hRfix, hRformula⟩ :=
    exists_cutoff_parameter_family β hβ χ hχ hχc hβzero
  let δ := min r (ε / 2)
  have hδ : 0 < δ := lt_min hr (by positivity)
  refine ⟨δ, hδ, R, hRzero, hR, hRinv, hRfix, ?_⟩
  intro t ht s
  have htr : t ∈ Icc (-r) r := by
    have hd := min_le_left r (ε / 2)
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [hRformula t htr s]
  by_cases hs : s ∈ tsupport χ
  · have htε : t ∈ ball (0 : Real) ε := by
      have hd := min_le_right r (ε / 2)
      rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [hεeq htε s hs]
  · simp only [image_eq_zero_of_notMem_tsupport hs, zero_mul]

section Strip

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners Real E H}

private theorem smooth_strip_transition
    (F : OpenPartialHomeomorph (Real × Real) M)
    (hFi : ContMDiffOn I 𝓘(Real, Real × Real) ∞ F.symm F.target)
    (q : Real × Real → M) {W : Set (Real × Real)}
    (hq : ContMDiffOn 𝓘(Real, Real × Real) I ∞ q W)
    (hqtarget : MapsTo q W F.target)
    (height : M → Real) (c : Real)
    (hheight : ∀ z ∈ F.source, height (F z) = c + z.2)
    (hqheight : ∀ z ∈ W, height (q z) = c + z.1) :
    ContDiffOn Real ∞ (fun z => (F.symm (q z)).1) W ∧
      ∀ z ∈ W, F ((F.symm (q z)).1, z.1) = q z := by
  have hcoord : ContDiffOn Real ∞ (fun z => F.symm (q z)) W :=
    (hFi.comp hq hqtarget).contDiffOn
  refine ⟨hcoord.fst, ?_⟩
  intro z hz
  have hqz := hqtarget hz
  have hback := F.right_inv hqz
  have ht := hheight (F.symm (q z)) (F.map_target hqz)
  rw [hback, hqheight z hz] at ht
  have hsnd : (F.symm (q z)).2 = z.1 := by linarith
  have heq : ((F.symm (q z)).1, z.1) = F.symm (q z) := Prod.ext rfl hsnd.symm
  rw [heq, hback]

private theorem exists_strip_parameter_family_of_endpoint_germ
    (F : OpenPartialHomeomorph (Real × Real) M)
    (hFi : ContMDiffOn I 𝓘(Real, Real × Real) ∞ F.symm F.target)
    (q : Real × Real → M) {W : Set (Real × Real)} (hW : IsOpen W)
    (hq : ContMDiffOn 𝓘(Real, Real × Real) I ∞ q W)
    (hqtarget : MapsTo q W F.target)
    (height : M → Real) (c : Real)
    (hheight : ∀ z ∈ F.source, height (F z) = c + z.2)
    (hqheight : ∀ z ∈ W, height (q z) = c + z.1)
    (χ : Real → Real) (hχ : ContDiff Real ∞ χ) (hχc : HasCompactSupport χ)
    (hWzero : ∀ s ∈ tsupport χ, (0, s) ∈ W)
    (hsource : ∀ s ∈ tsupport χ, (s, 0) ∈ F.source)
    (hcentral : ∀ s ∈ tsupport χ, q (0, s) = F (s, 0)) :
    ∃ r : Real, 0 < r ∧
      ∃ R : Real → Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞,
        (∀ s, R 0 s = s) ∧
        ContDiff Real ∞ (fun z : Real × Real => R z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × Real => (R z.1).symm z.2) ∧
        (∀ t s, s ∉ tsupport χ → R t s = s) ∧
        ∀ t ∈ Icc (-r) r, ∀ s, χ s = 1 →
          (t, s) ∈ W ∧ F (R t s, t) = q (t, s) := by
  obtain ⟨hα, hback⟩ := smooth_strip_transition F hFi q hq hqtarget height c hheight hqheight
  have hαzero (s : Real) (hs : s ∈ tsupport χ) : (F.symm (q (0, s))).1 = s := by
    rw [hcentral s hs, F.left_inv (hsource s hs)]
  obtain ⟨r, hr, R, hRzero, hR, hRinv, hRfix, hRformula⟩ :=
    exists_cutoff_parameter_family_of_contDiffOn (fun z => (F.symm (q z)).1) hW
      χ hχ hχc hWzero hα hαzero
  have hevent : ∀ᶠ t in 𝓝 (0 : Real), ∀ s ∈ tsupport χ, (t, s) ∈ W := by
    apply hχc.isCompact.eventually_forall_of_forall_eventually
    intro s hs
    exact hW.mem_nhds (hWzero s hs)
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp hevent
  let δ := min r (ε / 2)
  have hδ : 0 < δ := lt_min hr (by positivity)
  refine ⟨δ, hδ, R, hRzero, hR, hRinv, hRfix, ?_⟩
  intro t ht s hs
  have htr : t ∈ Icc (-r) r := by
    have hd := min_le_left r (ε / 2)
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have htε : t ∈ ball (0 : Real) ε := by
    have hd := min_le_right r (ε / 2)
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsK : s ∈ tsupport χ := subset_tsupport χ (by simp [Function.mem_support, hs])
  refine ⟨hεW htε s hsK, ?_⟩
  rw [hRformula t htr s, hs, one_mul, add_sub_cancel]
  exact hback (t, s) (hεW htε s hsK)

end Strip

private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

open Poincare.Manifold.Schoenflies.Plane

private theorem smooth_ambient_sphere_lift
    (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (q0 : S2)
    (y : Real × Real → E3) {W : Set (Real × Real)}
    (hy : ContDiffOn Real ∞ y W)
    (hmem : ∀ z ∈ W, y z ∈ F '' sphere (0 : E3) 1) :
    let q : Real × Real → S2 := fun z => unitRadialProjection q0 (F.symm (y z))
    ContMDiffOn 𝓘(Real, Real × Real) (𝓡 2) ∞ q W ∧
      ∀ z ∈ W, (q z : E3) = F.symm (y z) ∧ F (q z) = y z := by
  dsimp only
  have hunit (z : Real × Real) (hz : z ∈ W) : F.symm (y z) ∈ sphere (0 : E3) 1 := by
    obtain ⟨p, hp, heq⟩ := hmem z hz
    rw [← heq, F.symm_apply_apply]
    exact hp
  have hnonzero (z : Real × Real) (hz : z ∈ W) : F.symm (y z) ≠ 0 :=
    ne_zero_of_mem_unit_sphere ⟨F.symm (y z), hunit z hz⟩
  have hcomp : ContMDiffOn 𝓘(Real, Real × Real) (𝓡 3) ∞
      (fun z => F.symm (y z)) W :=
    F.symm.contMDiff.comp_contMDiffOn hy.contMDiffOn
  refine ⟨(contMDiffOn_unitRadialProjection (n := 2) (m := ∞) q0).comp hcomp
    (fun z hz => hnonzero z hz), ?_⟩
  intro z hz
  have hq : (unitRadialProjection q0 (F.symm (y z)) : E3) = F.symm (y z) :=
    congrArg Subtype.val (unitRadialProjection_apply_coe q0 ⟨F.symm (y z), hunit z hz⟩)
  exact ⟨hq, by rw [hq, F.apply_symm_apply]⟩

private theorem ambient_sphere_lift_eq_of_ambient_eq
    (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (q0 p : S2)
    {y : E3} (hy : y = F p) :
    unitRadialProjection q0 (F.symm y) = p := by
  rw [hy, F.symm_apply_apply, unitRadialProjection_apply_coe]

private theorem smooth_model_sphere_lift_of_common_neighborhood
    (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (q0 : S2)
    (g : S2 → E3) (U : Set E3)
    (hcommon : (F '' sphere (0 : E3) 1) ∩ U = range g ∩ U)
    (y : Real × Real → E3) {W : Set (Real × Real)}
    (hy : ContDiffOn Real ∞ y W)
    (hyactual : MapsTo y W (range g)) (hyU : MapsTo y W U) :
    let q : Real × Real → S2 := fun z => unitRadialProjection q0 (F.symm (y z))
    ContMDiffOn 𝓘(Real, Real × Real) (𝓡 2) ∞ q W ∧
      ∀ z ∈ W, (q z : E3) = F.symm (y z) ∧ F (q z) = y z := by
  apply smooth_ambient_sphere_lift F q0 y hy
  intro z hz
  have hactual : y z ∈ range g ∩ U := ⟨hyactual hz, hyU hz⟩
  rw [← hcommon] at hactual
  exact hactual.1

theorem exists_stationary_model_strip_coordinates
    (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (p₀ : S2)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (hFi : ContMDiffOn (𝓡 2) 𝓘(Real, Real × Real) ∞ F.symm F.target)
    (hheight : ∀ z ∈ F.source, G (F z) 2 = z.2)
    (g : S2 → E3) (U : Set E3)
    (hcommon : (G '' sphere (0 : E3) 1) ∩ U = range g ∩ U)
    (y : Real × Real → E3) {W : Set (Real × Real)} (hW : IsOpen W)
    (hy : ContDiffOn Real ∞ y W)
    (hyactual : MapsTo y W (range g)) (hyU : MapsTo y W U)
    (hyheight : ∀ z ∈ W, y z 2 = z.1)
    (hyvertical : ∀ z ∈ W, Saddle.toE2 (y z) = Saddle.toE2 (y (0, z.2)))
    (χ : Real → Real) (hχ : ContDiff Real ∞ χ) (hχc : HasCompactSupport χ)
    (hWzero : ∀ s ∈ tsupport χ, (0, s) ∈ W)
    (hsource : ∀ s ∈ tsupport χ, (s, 0) ∈ F.source)
    (hcentral : ∀ s ∈ tsupport χ, y (0, s) = G (F (s, 0))) :
    ∃ r : Real, 0 < r ∧
      ∃ R : Real → Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞,
        (∀ s, R 0 s = s) ∧
        ContDiff Real ∞ (fun z : Real × Real => R z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × Real => (R z.1).symm z.2) ∧
        (∀ t s, s ∉ tsupport χ → R t s = s) ∧
        ∀ t ∈ Icc (-r) r, ∀ s, χ s = 1 →
          G (F (R t s, t)) = y (t, s) ∧
          Saddle.toE2 (G (F (R t s, t))) = Saddle.toE2 (G (F (s, 0))) := by
  let q : Real × Real → S2 := fun z => unitRadialProjection p₀ (G.symm (y z))
  obtain ⟨hq, hqG⟩ := smooth_model_sphere_lift_of_common_neighborhood
    G p₀ g U hcommon y hy hyactual hyU
  change ContMDiffOn 𝓘(Real, Real × Real) (𝓡 2) ∞ q W at hq
  let W' := W ∩ q ⁻¹' F.target
  have hW' : IsOpen W' :=
    hq.continuousOn.isOpen_inter_preimage hW F.open_target
  have hqcentral (s : Real) (hs : s ∈ tsupport χ) : q (0, s) = F (s, 0) :=
    ambient_sphere_lift_eq_of_ambient_eq G p₀ _ (hcentral s hs)
  have hWzero' (s : Real) (hs : s ∈ tsupport χ) : (0, s) ∈ W' := by
    refine ⟨hWzero s hs, ?_⟩
    change q (0, s) ∈ F.target
    rw [hqcentral s hs]
    exact F.map_source (hsource s hs)
  obtain ⟨r, hr, R, hRzero, hR, hRinv, hRfix, hRmatch⟩ :=
    exists_strip_parameter_family_of_endpoint_germ F hFi q hW'
      (hq.mono inter_subset_left) (fun _ hz => hz.2)
      (fun p : S2 => G p 2) 0
      (fun z hz => by simpa only [zero_add] using hheight z hz)
      (fun z hz => by
        change G (q z) 2 = 0 + z.1
        rw [(hqG z hz.1).2, hyheight z hz.1, zero_add])
      χ hχ hχc hWzero' hsource hqcentral
  refine ⟨r, hr, R, hRzero, hR, hRinv, hRfix, ?_⟩
  intro t ht s hs
  obtain ⟨hz, hmatch⟩ := hRmatch t ht s hs
  have hsK : s ∈ tsupport χ := subset_tsupport χ (by simp [Function.mem_support, hs])
  have hGy : G (F (R t s, t)) = y (t, s) := by
    rw [hmatch]
    exact (hqG (t, s) hz.1).2
  exact ⟨hGy, by rw [hGy, hyvertical (t, s) hz.1, hcentral s hsK]⟩

end EndpointCoordinates

section CriticalGeometry

open Filter
open scoped _root_.Topology
set_option backward.isDefEq.respectTransparency false

private theorem critical_above_band_is_global_max {p : S2}
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0)
    (hupper : (13 / 10 : Real) < height p) :
    ∀ q : S2, height q ≤ height p := by
  obtain ⟨q, _, hqmax⟩ := isCompact_univ.exists_isMaxOn
    (show (univ : Set S2).Nonempty from ⟨p, mem_univ _⟩)
    height_contMDiff.continuous.continuousOn
  have hqmax' : IsLocalMax height q := hqmax.isLocalMax Filter.univ_mem
  have hqc : mfderiv (𝓡 2) 𝓘(Real, Real) height q = 0 := by
    have hc := Poincare.Geometry.Manifold.mfderiv_eq_zero_of_isLocalMin
      height_contMDiff.neg hqmax'.neg
    change mfderiv (𝓡 2) 𝓘(Real, Real) (-height) q = 0 at hc
    rw [mfderiv_neg] at hc
    exact neg_eq_zero.mp hc
  have hpU : p ∈ capRegion 2 := hupper
  have hqU : q ∈ capRegion 2 := hupper.trans_le (hqmax (mem_univ p))
  obtain ⟨z, hz⟩ := exists_unique_critical_in_each_cap
  have hpz : p = z 2 := (hz 2).2.2 p hpU hp
  have hqz : q = z 2 := (hz 2).2.2 q hqU hqc
  have hpq : p = q := hpz.trans hqz.symm
  intro x
  rw [hpq]
  exact hqmax (mem_univ x)

private theorem saddle_bounds_of_exists_higher {p : S2}
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0)
    (hlower : 1 < height p) (hhigher : ∃ q : S2, height p < height q) :
    height p ∈ Ioo (1 : Real) (41 / 40) ∧
      (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8) ∧
      ∀ q : S2, height q ∈ Icc (1 : Real) (13 / 10) →
        (mfderiv (𝓡 2) 𝓘(Real, Real) height q = 0 ↔ q = p) := by
  have hupper : height p ≤ (13 / 10 : Real) := by
    by_contra h
    obtain ⟨q, hq⟩ := hhigher
    exact (not_lt_of_ge (critical_above_band_is_global_max hp (lt_of_not_ge h) q)) hq
  have hlatitude := critical_latitude_in_saddle_interval_of_height_band hp ⟨hlower.le, hupper⟩
  exact ⟨⟨hlower, saddle_height_lt_fortyone_fortieths hp hlatitude⟩, hlatitude,
    critical_in_height_band_iff_eq_saddle hp hlatitude⟩

private theorem saddle_bounds_of_local_normal_form {p : S2}
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0)
    (hlower : 1 < height p) (d : E2 → S2) {r : Real} (hr : 0 < r)
    (hform : ∀ x ∈ closedBall (0 : E2) r,
      height (d x) = height p - (x 0)^2 + (x 1)^2) :
    height p ∈ Ioo (1 : Real) (41 / 40) ∧
      (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8) ∧
      ∀ q : S2, height q ∈ Icc (1 : Real) (13 / 10) →
        (mfderiv (𝓡 2) 𝓘(Real, Real) height q = 0 ↔ q = p) := by
  apply saddle_bounds_of_exists_higher hp hlower
  let x : E2 := EuclideanSpace.single 1 (r / 2)
  have hx : x ∈ closedBall (0 : E2) r := by
    rw [mem_closedBall_zero_iff]
    dsimp [x]
    simp only [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < r / 2)]
    linarith
  refine ⟨d x, ?_⟩
  rw [hform x hx]
  simp only [x, PiLp.single_apply, Fin.isValue,
    zero_ne_one, ↓reduceIte]
  nlinarith [sq_pos_of_pos (by positivity : 0 < r / 2)]

private theorem saddle_bounds_of_morse_chart_on_closedBall {p : S2}
    (hlower : 1 < height p) (d : OpenPartialHomeomorph E2 S2)
    (hd0 : 0 ∈ d.source) (hdp : d 0 = p)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    {r : Real} (hr : 0 < r)
    (hform : ∀ x ∈ closedBall (0 : E2) r,
      height (d x) = height p - (x 0)^2 + (x 1)^2) :
    mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0 ∧
      height p ∈ Ioo (1 : Real) (41 / 40) ∧
      (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8) ∧
      ∀ q : S2, height q ∈ Icc (1 : Real) (13 / 10) →
        (mfderiv (𝓡 2) 𝓘(Real, Real) height q = 0 ↔ q = p) := by
  have heq : height ∘ d =ᶠ[𝓝 (0 : E2)]
      (fun x => height p + ∑ i : Fin 2, (![-1, 1] i : Real) * (x i)^2) := by
    filter_upwards [closedBall_mem_nhds (0 : E2) hr] with x hx
    rw [Function.comp_apply, hform x hx]
    simp [Fin.sum_univ_two]
    ring
  have hcritical : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0 := by
    rw [← hdp, mfderiv_eq_zero_iff_fderiv_of_sphere_coordinates_eventuallyEq
      height_contMDiff d hd hdi hd0 heq]
    exact (Poincare.Analysis.Calculus.Morse.fderiv_diagonal_quadratic_eq_zero_iff
      (height p) ![-1, 1] (by intro i; fin_cases i <;> norm_num) 0).mpr rfl
  exact ⟨hcritical, saddle_bounds_of_local_normal_form hcritical hlower d hr hform⟩

private theorem critical_fiber_radicand_factor
    {x₀ z₀ c : Real} (hnorm : x₀ ^ 2 + z₀ ^ 2 = 1)
    (hcrit : x₀ * (2 * z₀ - 1) + (3 / 10) * z₀ = 0)
    (hc : c = 1 + z₀ - z₀ ^ 2 + (3 / 10) * x₀) (z : Real) :
    1 - z ^ 2 - ((10 / 3 : Real) * (c - 1 - z + z ^ 2)) ^ 2 =
      (z - z₀) ^ 2 * (-1 - (20 / 3 : Real) * x₀ -
        (100 / 9 : Real) * (z + z₀ - 1) ^ 2) := by
  have hn : 1 - x₀ ^ 2 - z₀ ^ 2 = 0 := by linarith
  calc
    _ = (z - z₀) ^ 2 * (-1 - (20 / 3 : Real) * x₀ -
          (100 / 9 : Real) * (z + z₀ - 1) ^ 2) +
        (1 - x₀ ^ 2 - z₀ ^ 2) -
        (20 / 3 : Real) * (z - z₀) * (x₀ * (2 * z₀ - 1) + (3 / 10) * z₀) := by
      rw [hc]
      ring
    _ = _ := by rw [hn, hcrit]; ring

private theorem critical_fiber_quadratic_pos
    {x₀ z₀ : Real} (hnorm : x₀ ^ 2 + z₀ ^ 2 = 1)
    (hcrit : x₀ * (2 * z₀ - 1) + (3 / 10) * z₀ = 0)
    (hz : z₀ ∈ Ioo (3 / 5 : Real) (5 / 8)) :
    0 < -1 - (20 / 3 : Real) * x₀ - (100 / 9 : Real) * (2 * z₀ - 1) ^ 2 := by
  have hx : x₀ < 0 := by
    by_contra hh
    have hmul : 0 ≤ x₀ * (2 * z₀ - 1) :=
      mul_nonneg (le_of_not_gt hh) (by linarith [hz.1])
    nlinarith [hz.1]
  have hxb : x₀ < -(3 / 4 : Real) := by nlinarith [hz.1, hz.2]
  have hsq : (2 * z₀ - 1) ^ 2 < (1 / 16 : Real) := by
    nlinarith [hz.1, hz.2]
  nlinarith

theorem isConnected_critical_level_of_saddle_latitude
    {p : S2} (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0)
    (hpz : (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8)) :
    IsConnected (height ⁻¹' {height p}) := by
  let x₀ : Real := (p : E3) 0
  let z₀ : Real := (p : E3) 2
  obtain ⟨hpy, hcrit⟩ := critical_point_coordinates hp
  have hnorm : x₀ ^ 2 + z₀ ^ 2 = 1 := by
    have hn := EuclideanSpace.norm_sq_eq (p : E3)
    simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, hpy] at hn
    exact hn.symm
  have hc : height p = 1 + z₀ - z₀ ^ 2 + (3 / 10) * x₀ := by
    rw [height_apply, hpy]
    change z₀ + x₀ ^ 2 + 0 ^ 2 + (3 / 10 : Real) * x₀ = _
    nlinarith
  let X : Real → Real := fun z => (10 / 3 : Real) * (height p - 1 - z + z ^ 2)
  let R : Real → Real := fun z => 1 - z ^ 2 - (X z) ^ 2
  let Q : Real → Real := fun z =>
    -1 - (20 / 3 : Real) * x₀ - (100 / 9 : Real) * (z + z₀ - 1) ^ 2
  have hfactor (z : Real) : R z = (z - z₀) ^ 2 * Q z :=
    critical_fiber_radicand_factor hnorm hcrit hc z
  have hQ₀ : 0 < Q z₀ := by
    change 0 < -1 - (20 / 3 : Real) * x₀ - (100 / 9 : Real) * (z₀ + z₀ - 1) ^ 2
    convert critical_fiber_quadratic_pos hnorm hcrit hpz using 1
    ring
  let M : Real := -1 - (20 / 3 : Real) * x₀
  have hM : 0 < M := by
    have hsq : 0 ≤ (100 / 9 : Real) * (z₀ + z₀ - 1) ^ 2 := by positivity
    change 0 < M - _ at hQ₀
    linarith
  let r : Real := (3 / 10 : Real) * Real.sqrt M
  let center : Real := 1 - z₀
  have hr : 0 < r := mul_pos (by norm_num) (Real.sqrt_pos.mpr hM)
  have hrsq : r ^ 2 = (9 / 100 : Real) * M := by
    dsimp [r]
    rw [mul_pow, Real.sq_sqrt hM.le]
    ring
  have hQiff (z : Real) : 0 ≤ Q z ↔ z ∈ Icc (center - r) (center + r) := by
    have hQeq : Q z = M - (100 / 9 : Real) * (z - center) ^ 2 := by
      dsimp [Q, M, center]
      ring
    rw [hQeq]
    constructor
    · intro h
      have hsq : (z - center) ^ 2 ≤ r ^ 2 := by nlinarith
      have habs : |z - center| ≤ r := (sq_le_sq₀ (abs_nonneg _) hr.le).mp (by
        simpa only [sq_abs] using hsq)
      obtain ⟨hl, hu⟩ := abs_le.mp habs
      exact ⟨by linarith, by linarith⟩
    · intro hz
      have hh := mul_nonneg (sub_nonneg.mpr hz.1) (sub_nonneg.mpr hz.2)
      nlinarith
  have hRiff (z : Real) : 0 ≤ R z ↔ z ∈ Icc (center - r) (center + r) := by
    rw [← hQiff]
    constructor
    · intro h
      by_cases hz : z = z₀
      · simpa only [hz] using hQ₀.le
      have hs : 0 < (z - z₀) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hz)
      rw [hfactor] at h
      exact nonneg_of_mul_nonneg_right h hs
    · intro h
      rw [hfactor]
      exact mul_nonneg (sq_nonneg _) h
  let arc : Real → Real → E3 := fun sign z => vector (X z) (sign * Real.sqrt (R z)) z
  have harc (sign : Real) : Continuous (arc sign) := by
    dsimp [arc, X, R, vector]
    fun_prop
  have harcMem {sign z : Real} (hsign : sign ^ 2 = 1)
      (hz : z ∈ Icc (center - r) (center + r)) : arc sign z ∈ sphere (0 : E3) 1 := by
    have hrad := (hRiff z).mpr hz
    have hn := EuclideanSpace.norm_sq_eq (arc sign z)
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, arc,
      vector_zero, vector_one, vector_two, mul_pow, hsign, one_mul,
      Real.sq_sqrt hrad] at hn
    rw [mem_sphere_zero_iff_norm]
    dsimp [R] at hn
    nlinarith [norm_nonneg (arc sign z)]
  have harcHeight {sign z : Real} (hsign : sign ^ 2 = 1)
      (hz : z ∈ Icc (center - r) (center + r)) :
      height ⟨arc sign z, harcMem hsign hz⟩ = height p := by
    rw [height_apply]
    simp only [arc, vector_zero, vector_one, vector_two, mul_pow, hsign,
      one_mul, Real.sq_sqrt ((hRiff z).mpr hz)]
    dsimp [R, X]
    ring
  have hpoint (q : S2) (hq : height q = height p) :
      (q : E3) 0 = X ((q : E3) 2) ∧ ((q : E3) 1) ^ 2 = R ((q : E3) 2) := by
    have hn := EuclideanSpace.norm_sq_eq (q : E3)
    simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] at hn
    have hheight := height_apply q
    have hx : (q : E3) 0 = X ((q : E3) 2) := by dsimp [X]; nlinarith
    refine ⟨hx, ?_⟩
    dsimp [R]
    rw [← hx]
    nlinarith
  have himage : (Subtype.val : S2 → E3) '' (height ⁻¹' {height p}) =
      arc 1 '' Icc (center - r) (center + r) ∪
        arc (-1) '' Icc (center - r) (center + r) := by
    apply Subset.antisymm
    · rintro q ⟨q, hq, rfl⟩
      obtain ⟨hx, hy⟩ := hpoint q hq
      have hz : (q : E3) 2 ∈ Icc (center - r) (center + r) :=
        (hRiff _).mp (hy ▸ sq_nonneg ((q : E3) 1))
      have hsqrt : Real.sqrt (R ((q : E3) 2)) = |(q : E3) 1| := by
        rw [← hy, Real.sqrt_sq_eq_abs]
      by_cases hypos : 0 ≤ (q : E3) 1
      · left
        refine ⟨(q : E3) 2, hz, ?_⟩
        ext i
        fin_cases i <;> simp [arc, hx, hsqrt, abs_of_nonneg hypos]
      · right
        refine ⟨(q : E3) 2, hz, ?_⟩
        ext i
        fin_cases i <;> simp [arc, hx, hsqrt, abs_of_neg (lt_of_not_ge hypos)]
    · rintro q (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact ⟨⟨arc 1 z, harcMem (by norm_num) hz⟩,
          harcHeight (by norm_num) hz, rfl⟩
      · exact ⟨⟨arc (-1) z, harcMem (by norm_num) hz⟩,
          harcHeight (by norm_num) hz, rfl⟩
  have hconn : IsConnected (Icc (center - r) (center + r)) :=
    isConnected_Icc (by linarith)
  have hz₀ : z₀ ∈ Icc (center - r) (center + r) := (hQiff z₀).mp hQ₀.le
  have hR₀ : R z₀ = 0 := by rw [hfactor]; simp
  have hagree : arc (-1) z₀ = arc 1 z₀ := by simp [arc, hR₀]
  have hconnImage : IsConnected ((Subtype.val : S2 → E3) '' (height ⁻¹' {height p})) := by
    rw [himage]
    exact (hconn.image _ (harc 1).continuousOn).union
      ⟨arc 1 z₀, ⟨z₀, hz₀, rfl⟩, ⟨z₀, hz₀, hagree⟩⟩
      (hconn.image _ (harc (-1)).continuousOn)
  exact ⟨hconnImage.nonempty.of_image,
    Topology.IsInducing.subtypeVal.isPreconnected_image.mp hconnImage.2⟩

theorem critical_fiber_geometry_of_matching
    (f : S2 → E3) (v : E3) (c : Real)
    (e d : OpenPartialHomeomorph E2 S2) (p₀ : S2)
    (hp₀ : 1 < height p₀) (hd0 : 0 ∈ d.source) (hdp : d 0 = p₀)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    (F : E3 → E3) {s ρ : Real} (hs : 0 < s) (hρ : 0 < ρ)
    (he : ∀ x ∈ closedBall (0 : E2) ρ, Real.sqrt s • x ∈ e.source)
    (hactual : ∀ x ∈ e.source, inner Real v (f (e x)) = c - (x 0)^2 + (x 1)^2)
    (hmodel : ∀ q : S2, inner Real v (F q) = c + s * (height q - height p₀))
    (hmatch : ∀ x ∈ closedBall (0 : E2) ρ,
      F (d x) = f (e (Real.sqrt s • x))) :
    (∀ x ∈ closedBall (0 : E2) ρ,
      height (d x) = height p₀ - (x 0)^2 + (x 1)^2) ∧
    mfderiv (𝓡 2) 𝓘(Real, Real) height p₀ = 0 ∧
    height p₀ ∈ Ioo (1 : Real) (41 / 40) ∧
    (p₀ : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8) ∧
    IsConnected (height ⁻¹' {height p₀}) ∧
    ∀ q : S2, height q ∈ Icc (1 : Real) (13 / 10) →
      (mfderiv (𝓡 2) 𝓘(Real, Real) height q = 0 ↔ q = p₀) := by
  have hform (x : E2) (hx : x ∈ closedBall (0 : E2) ρ) :
      height (d x) = height p₀ - (x 0)^2 + (x 1)^2 := by
    have heq := congrArg (fun y => inner Real v y) (hmatch x hx)
    rw [hmodel, hactual _ (he x hx)] at heq
    simp only [PiLp.smul_apply, smul_eq_mul, mul_pow, Real.sq_sqrt hs.le] at heq
    nlinarith
  obtain ⟨hcritical, hheight, hlatitude, hunique⟩ :=
    saddle_bounds_of_morse_chart_on_closedBall hp₀ d hd0 hdp hd hdi hρ hform
  exact ⟨hform, hcritical, hheight, hlatitude,
    isConnected_critical_level_of_saddle_latitude hcritical hlatitude, hunique⟩

end CriticalGeometry

section ModelStrips

open SaddleLevel
open Filter
open scoped _root_.Topology
local notation "IR" => 𝓘(Real, Real)
local notation "IR2" => 𝓘(Real, Real × Real)
set_option backward.isDefEq.respectTransparency false

private theorem exists_whole_band_exterior_strips
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {p : S2} (hunique : ∀ q, h q = h p →
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q = p)
    (hconnected : IsPreconnected (h ⁻¹' {h p}))
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, h (e x) = h p - x 0 ^ 2 + x 1 ^ 2)
    {r epsilon : Real} (hr : 0 < r) (hrs : closedSquare r ⊆ e.source)
    (hepsilon : 0 < epsilon) :
    ∃ (a b a₀ b₀ : Fin 2 → Real) (eta : Real)
        (F : Fin 2 → OpenPartialHomeomorph (Real × Real) S2),
      0 < eta ∧ eta < epsilon ∧
      (∀ i, a i < a₀ i ∧ a₀ i < b₀ i ∧ b₀ i < b i) ∧
      (∀ i, Icc (a i) (b i) ×ˢ Icc (-eta) eta ⊆ (F i).source) ∧
      (∀ i, ContMDiffOn IR2 (𝓡 2) ∞ (F i) (F i).source) ∧
      (∀ i, ContMDiffOn (𝓡 2) IR2 ∞ (F i).symm (F i).target) ∧
      (∀ i z, z ∈ (F i).source → h (F i z) = h p + z.2) ∧
      (⋃ i, F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
        (h ⁻¹' {h p}) \ e '' openSquare r ∧
      Pairwise (fun i j => Disjoint (F i).target (F j).target) ∧
      (∀ i, range (fun j : Fin 2 × Fin 2 => e (contact r j)) ∩
          (F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
        {F i (a₀ i, 0), F i (b₀ i, 0)}) ∧
      h ⁻¹' Icc (h p - eta) (h p + eta) ⊆ e '' openSquare r ∪
        ⋃ i, F i '' (Icc (a i) (b i) ×ˢ Icc (-eta) eta) := by
  have hcomponent : connectedComponentIn (h ⁻¹' {h p}) p = h ⁻¹' {h p} :=
    hconnected.connectedComponentIn rfl
  obtain ⟨a₀, b₀, w, F, hw, hab, hFs, hF, hFi, hheight, hcentral,
      hdisj, hends, _⟩ :=
    exists_disjoint_actual_exterior_strips hh hunique e he0 hep he hei hform hr hrs
  change _ = connectedComponentIn (h ⁻¹' {h p}) p \ _ at hcentral
  rw [hcomponent] at hcentral
  let a : Fin 2 → Real := fun i => a₀ i - w / 2
  let b : Fin 2 → Real := fun i => b₀ i + w / 2
  let V : Fin 2 → Set (Real × Real) :=
    fun i => Ioo (a i) (b i) ×ˢ Ioo (-w / 2) (w / 2)
  have hVsub (i : Fin 2) : V i ⊆ (F i).source := by
    intro z hz
    rw [hFs i]
    dsimp [V, a, b] at hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  have hVopen (i : Fin 2) : IsOpen (F i '' V i) :=
    (F i).isOpen_image_of_subset_source (isOpen_Ioo.prod isOpen_Ioo) (hVsub i)
  let O : Set S2 := e '' openSquare r ∪ ⋃ i, F i '' V i
  have hO : IsOpen O :=
    (e.isOpen_image_of_subset_source (isOpen_openSquare r)
      ((openSquare_subset_closedSquare r).trans hrs)).union (isOpen_iUnion hVopen)
  have hfiber : h ⁻¹' {h p} ⊆ O := by
    intro q hq
    by_cases hqp : q ∈ e '' openSquare r
    · exact Or.inl hqp
    · right
      obtain ⟨i, z, hz, heq⟩ := mem_iUnion.mp (hcentral.superset ⟨hq, hqp⟩)
      have ht : z.2 = 0 := hz.2
      refine mem_iUnion_of_mem i ⟨z, ?_, heq⟩
      dsimp [V, a, b]
      exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
        ⟨by linarith, by linarith⟩⟩
  obtain ⟨delta, hdelta, hcover⟩ :=
    Poincare.Topology.exists_closedBand_subset_of_fiber_subset_open hh.continuous hO hfiber
  let eta : Real := min delta (min (w / 2) epsilon) / 2
  have heta : 0 < eta := half_pos (lt_min hdelta (lt_min (half_pos hw) hepsilon))
  have heta_delta : eta ≤ delta :=
    (half_le_self (le_min hdelta.le (le_min (half_pos hw).le hepsilon.le))).trans
      (min_le_left _ _)
  have heta_w : eta < w / 2 :=
    (half_lt_self (lt_min hdelta (lt_min (half_pos hw) hepsilon))).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have heta_epsilon : eta < epsilon :=
    (half_lt_self (lt_min hdelta (lt_min (half_pos hw) hepsilon))).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨a, b, a₀, b₀, eta, F, heta, heta_epsilon, ?_, ?_, hF, hFi,
    hheight, hcentral, hdisj, hends, ?_⟩
  · intro i
    exact ⟨by dsimp [a]; linarith, hab i, by dsimp [b]; linarith⟩
  · intro i z hz
    rw [hFs i]
    dsimp [a, b] at hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  · intro q hq
    have hqO : q ∈ O := hcover ⟨by linarith [hq.1], by linarith [hq.2]⟩
    rcases hqO with hqp | hqs
    · exact Or.inl hqp
    · right
      obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hqs
      have hzheight := hheight i z (hVsub i hz)
      refine mem_iUnion_of_mem i ⟨z, ?_, rfl⟩
      exact ⟨⟨hz.1.1.le, hz.1.2.le⟩,
        ⟨by linarith [hq.1], by linarith [hq.2]⟩⟩

private theorem exists_exact_whole_level_exterior_strips
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {p : S2} (hunique : ∀ q, h q = h p →
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q = p)
    (hconnected : IsPreconnected (h ⁻¹' {h p}))
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, h (e x) = h p - x 0 ^ 2 + x 1 ^ 2)
    {r epsilon : Real} (hr : 0 < r) (hrs : closedSquare r ⊆ e.source)
    (hepsilon : 0 < epsilon) :
    ∃ (a b a₀ b₀ : Fin 2 → Real) (eta δ : Real)
        (F : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
        (L : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2)) (A B : Fin 2 → Real → Real),
      0 < δ ∧ δ < eta ∧ eta < epsilon ∧ δ < r ^ 2 ∧
      (∀ i, a i < a₀ i ∧ a₀ i < b₀ i ∧ b₀ i < b i) ∧
      (∀ i, Icc (a i) (b i) ×ˢ Icc (-eta) eta ⊆ (F i).source) ∧
      (∀ i, ContMDiffOn IR2 (𝓡 2) ∞ (F i) (F i).source) ∧
      (∀ i, ContMDiffOn (𝓡 2) IR2 ∞ (F i).symm (F i).target) ∧
      (∀ i z, z ∈ (F i).source → h (F i z) = h p + z.2) ∧
      Pairwise (fun i j => Disjoint (F i).target (F j).target) ∧
      (∀ k, F k.1 (stripEndpoint a₀ b₀ k, 0) = e (contact r (L k))) ∧
      (∀ i, A i 0 = a₀ i ∧ B i 0 = b₀ i) ∧
      ∀ t ∈ Icc (-δ) δ,
        (∀ i, ContinuousAt (A i) t ∧ ContinuousAt (B i) t ∧
          a i < A i t ∧ A i t < B i t ∧ B i t < b i ∧
          (Icc (A i t) (B i t) ×ˢ ({t} : Set Real) ⊆ (F i).source) ∧
          F i (A i t, t) = e (movingContact r t (L (i, 0))) ∧
          F i (B i t, t) = e (movingContact r t (L (i, 1))) ∧
          (∀ s ∈ Icc (a i) (b i),
            F i (s, t) ∉ e '' openSquare r ↔ s ∈ Icc (A i t) (B i t))) ∧
        ((h ⁻¹' {h p + t}) \ e '' openSquare r) =
          ⋃ i, F i '' (Icc (A i t) (B i t) ×ˢ ({t} : Set Real)) := by
  obtain ⟨a, b, a₀, b₀, eta, F, heta, heta_epsilon, hchain, hrect,
      hF, hFi, hheight, hcentral, hdisjoint, hends, hband⟩ :=
    exists_whole_band_exterior_strips hh hunique hconnected e he0 hep he hei
      hform hr hrs hepsilon
  obtain ⟨δ, L, A, B, hδ, hδeta, hδr, hL, hzero, hcuts⟩ :=
    exists_recut_exterior_strips e hr hrs hform F a b a₀ b₀ heta hchain hrect
      hheight hdisjoint hcentral hends hband
  exact ⟨a, b, a₀, b₀, eta, δ, F, L, A, B, hδ, hδeta, heta_epsilon,
    hδr, hchain, hrect, hF, hFi, hheight, hdisjoint, hL, hzero, hcuts⟩

theorem exists_exact_nested_exterior_strips
    {p : S2} (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0)
    (hpz : (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8))
    (d : OpenPartialHomeomorph E2 S2)
    (hd0 : 0 ∈ d.source) (hdp : d 0 = p)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    (hform : ∀ x ∈ d.source, height (d x) = height p - x 0 ^ 2 + x 1 ^ 2)
    {r epsilon : Real} (hr : 0 < r) (hrs : closedSquare r ⊆ d.source)
    (hepsilon : 0 < epsilon) :
    ∃ (a b a₀ b₀ : Fin 2 → Real) (eta δ : Real)
        (F : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
        (L : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2)) (A B : Fin 2 → Real → Real),
      0 < δ ∧ δ < eta ∧ eta < epsilon ∧ δ < r ^ 2 ∧
      (∀ i, a i < a₀ i ∧ a₀ i < b₀ i ∧ b₀ i < b i) ∧
      (∀ i, Icc (a i) (b i) ×ˢ Icc (-eta) eta ⊆ (F i).source) ∧
      (∀ i, ContMDiffOn IR2 (𝓡 2) ∞ (F i) (F i).source) ∧
      (∀ i, ContMDiffOn (𝓡 2) IR2 ∞ (F i).symm (F i).target) ∧
      (∀ i z, z ∈ (F i).source → height (F i z) = height p + z.2) ∧
      Pairwise (fun i j => Disjoint (F i).target (F j).target) ∧
      (∀ k, F k.1 (stripEndpoint a₀ b₀ k, 0) = d (contact r (L k))) ∧
      (∀ i, A i 0 = a₀ i ∧ B i 0 = b₀ i) ∧
      ∀ t ∈ Icc (-δ) δ,
        (∀ i, ContinuousAt (A i) t ∧ ContinuousAt (B i) t ∧
          a i < A i t ∧ A i t < B i t ∧ B i t < b i ∧
          (Icc (A i t) (B i t) ×ˢ ({t} : Set Real) ⊆ (F i).source) ∧
          F i (A i t, t) = d (movingContact r t (L (i, 0))) ∧
          F i (B i t, t) = d (movingContact r t (L (i, 1))) ∧
          (∀ s ∈ Icc (a i) (b i),
            F i (s, t) ∉ d '' openSquare r ↔ s ∈ Icc (A i t) (B i t))) ∧
        ((height ⁻¹' {height p + t}) \ d '' openSquare r) =
          ⋃ i, F i '' (Icc (A i t) (B i t) ×ˢ ({t} : Set Real)) := by
  obtain ⟨p₀, hp₀z, hp₀height, hp₀crit, _⟩ := exists_unique_critical_point_in_height_band
  have hpp₀ : p = p₀ := critical_latitude_unique_in_saddle_interval hp hp₀crit
    (Ioo_subset_Icc_self hpz) (Ioo_subset_Icc_self hp₀z)
  have hpheight : height p ∈ Ioo (1 : Real) (41 / 40) := hpp₀ ▸ hp₀height
  have hunique (q : S2) (hq : height q = height p)
      (hqcrit : mfderiv (𝓡 2) 𝓘(Real, Real) height q = 0) : q = p := by
    apply (critical_in_height_band_iff_eq_saddle hp hpz q ?_).mp hqcrit
    rw [hq]
    exact ⟨hpheight.1.le, by linarith [hpheight.2]⟩
  exact exists_exact_whole_level_exterior_strips height_contMDiff hunique
    (isConnected_critical_level_of_saddle_latitude hp hpz).isPreconnected
    d hd0 hdp hd hdi hform hr hrs hepsilon

private theorem contDiff_toE2 : ContDiff Real ∞ toE2 := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff
  · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff

private theorem contDiff_toE3 (c : Real) : ContDiff Real ∞ (fun x => toE3 x c) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff
  · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff
  · exact contDiff_const

private theorem exists_protected_slab_neighborhood
    (Q : Set E3) (hQ : IsCompact Q) {U : Set E3} (hU : IsOpen U)
    (hQU : Q ⊆ U) (B : Set E2) (hB : IsCompact B)
    (havoid : Disjoint (toE2 '' (Q ∩ {y : E3 | y 2 = 0})) B) :
    ∃ (δ : Real) (C O : Set E2) (V : Set E3),
      0 < δ ∧ IsCompact C ∧ IsOpen O ∧ O ⊆ C ∧
      toE2 '' (Q ∩ {y : E3 | y 2 = 0}) ⊆ O ∧ Disjoint C B ∧
      (∀ t ∈ Icc (-δ) δ, ∀ x ∈ C, toE3 x t ∈ U) ∧
      (∀ y ∈ Q, y 2 ∈ Icc (-δ) δ → toE2 y ∈ O) ∧
      IsOpen V ∧ Q ⊆ V ∧
      ∀ t ∈ Icc (-δ) δ, ∀ x, toE3 x t ∈ V → x ∈ O := by
  have hz : Continuous (fun y : E3 => y 2) :=
    (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).continuous
  let P : Set E2 := toE2 '' (Q ∩ {y : E3 | y 2 = 0})
  have hP : IsCompact P :=
    (hQ.inter_right (isClosed_eq hz continuous_const)).image contDiff_toE2.continuous
  let A : Set E2 := (fun x => toE3 x 0) ⁻¹' U \ B
  have hA : IsOpen A := (hU.preimage (contDiff_toE3 0).continuous).sdiff hB.isClosed
  have hPA : P ⊆ A := by
    rintro x ⟨y, ⟨hyQ, hy0⟩, rfl⟩
    have heq : toE3 (toE2 y) 0 = y := by
      ext i
      fin_cases i <;> simp_all [toE2, toE3]
    refine ⟨?_, fun hxB => Set.disjoint_left.mp havoid ⟨y, ⟨hyQ, hy0⟩, rfl⟩ hxB⟩
    change toE3 (toE2 y) 0 ∈ U
    rw [heq]
    exact hQU hyQ
  obtain ⟨O, hO, hPO, hOA, hC⟩ := exists_open_between_and_isCompact_closure hP hA hPA
  let C : Set E2 := closure O
  have hCB : Disjoint C B := Set.disjoint_left.mpr (fun _ hx hy => (hOA hx).2 hy)
  have hlift : Continuous (fun z : Real × E2 => toE3 z.2 z.1) := by
    apply ContDiff.continuous (n := ∞) (𝕜 := Real)
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.comp contDiff_snd
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff.comp contDiff_snd
    · exact contDiff_fst
  have hcentral : ({0} : Set Real) ×ˢ C ⊆ (fun z : Real × E2 => toE3 z.2 z.1) ⁻¹' U := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    have ht0 : t = 0 := ht
    subst t
    exact (hOA hx).1
  obtain ⟨T, Z, hT, _, h0T, hCZ, hTZ⟩ := generalized_tube_lemma
    isCompact_singleton hC (hU.preimage hlift) hcentral
  obtain ⟨ρ, hρ, hρT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds (h0T rfl))
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  obtain ⟨d, hd, hband⟩ :=
    Poincare.Topology.exists_closedBand_subset_of_fiber_subset_open
      (h := fun q : Q => (q : E3) 2)
      (hz.comp continuous_subtype_val) (hO.preimage (contDiff_toE2.continuous.comp continuous_subtype_val))
      (c := 0) (by
        intro y hy
        exact hPO ⟨(y : E3), ⟨y.property, hy⟩, rfl⟩)
  let δ : Real := min d (ρ / 2)
  have hδ : 0 < δ := lt_min hd (half_pos hρ)
  have hδd : δ ≤ d := min_le_left _ _
  have hδρ : δ ≤ ρ / 2 := min_le_right _ _
  have hnear (y : E3) (hy : y ∈ Q) (ht : y 2 ∈ Icc (-δ) δ) : toE2 y ∈ O := by
    exact hband (a := ⟨y, hy⟩) ⟨by change 0 - d ≤ y 2; linarith [ht.1],
      by change y 2 ≤ 0 + d; linarith [ht.2]⟩
  let V : Set E3 := toE2 ⁻¹' O ∪ {y | δ < |y 2|}
  have hV : IsOpen V :=
    (hO.preimage contDiff_toE2.continuous).union (isOpen_lt continuous_const hz.abs)
  refine ⟨δ, C, O, V, hδ, hC, hO, subset_closure, hPO, hCB, ?_, hnear, hV, ?_, ?_⟩
  · intro t ht x hx
    apply hTZ (a := (t, x)) ⟨hρT ?_, hCZ hx⟩
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro y hy
    by_cases ht : y 2 ∈ Icc (-δ) δ
    · exact Or.inl (hnear y hy ht)
    · exact Or.inr (lt_of_not_ge (fun h => ht (abs_le.mp h)))
  · intro t ht x hx
    rcases hx with hx | hx
    · have heq : toE2 (toE3 x t) = x := by ext i; fin_cases i <;> rfl
      simpa only [mem_preimage, heq] using hx
    · exact False.elim ((not_lt_of_ge (abs_le.mpr ht)) hx)

private theorem planar_strip_geometry
    (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (hF : ContMDiffOn IR2 (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) IR2 ∞ F.symm F.target)
    (H : Real → Real)
    (hheight : ∀ z ∈ F.source, G (F z) 2 = H z.2) :
    let μ : Real × Real → E2 := fun z => toE2 (G (F (z.2, z.1)))
    ContDiffOn Real ∞ μ (Prod.swap ⁻¹' F.source) ∧
      (∀ t : Real, InjOn (fun s => μ (t, s)) {s | (s, t) ∈ F.source}) ∧
      ∀ t s : Real, (s, t) ∈ F.source → deriv (fun y => μ (t, y)) s ≠ 0 := by
  dsimp only
  let g : S2 → E3 := fun p => G p
  have hg : ContMDiff (𝓡 2) (𝓡 3) ∞ g :=
    G.contMDiff.comp (contMDiff_coe_sphere (n := 2) (m := ∞) (E := E3))
  have hgd (p : S2) : Injective (mfderiv (𝓡 2) (𝓡 3) g p) := by
    rw [show g = G ∘ (Subtype.val : S2 → E3) from rfl,
      mfderiv_comp p (G.contMDiff.mdifferentiable (by simp) (p : E3))
        ((contMDiff_coe_sphere (n := 2) (m := ∞) (E := E3) p).mdifferentiableAt (by simp))]
    apply (G.mfderivToContinuousLinearEquiv (by simp) (p : E3)).injective.comp
    convert! injective_mvfderiv_subtypeVal_sphere p
  have hμ : ContDiffOn Real ∞ (fun z : Real × Real => toE2 (G (F (z.2, z.1))))
      (Prod.swap ⁻¹' F.source) := by
    apply ((contDiff_toE2.contMDiff.comp hg).comp_contMDiffOn hF).contDiffOn.comp
      (contDiff_snd.prodMk contDiff_fst).contDiffOn
    intro z hz
    exact hz
  refine ⟨hμ, ?_, ?_⟩
  · intro t s hs u hu heq
    have hfull : G (F (s, t)) = G (F (u, t)) := by
      ext i
      fin_cases i
      · exact congrArg (fun x : E2 => x 0) heq
      · exact congrArg (fun x : E2 => x 1) heq
      · exact (hheight (s, t) hs).trans (hheight (u, t) hu).symm
    exact congrArg Prod.fst (F.injOn hs hu (Subtype.ext (G.injective hfull)))
  · intro t s hs
    let k : Real → S2 := fun y => F (y, t)
    have hpair : ContMDiff IR IR2 ∞ (fun y : Real => (y, t)) :=
      (contDiff_id.prodMk contDiff_const).contMDiff
    have hpd : HasFDerivAt (fun y : Real => (y, t))
        (ContinuousLinearMap.inl Real Real Real) s :=
      (hasFDerivAt_id s).prodMk (hasFDerivAt_const t s)
    have hpairder : Injective (mfderiv IR IR2 (fun y : Real => (y, t)) s) := by
      rw [mfderiv_eq_fderiv, hpd.fderiv]
      intro x y hxy
      exact congrArg Prod.fst hxy
    have hk : ContMDiffAt IR (𝓡 2) ∞ k s :=
      (hF.contMDiffAt (F.open_source.mem_nhds hs)).comp s (hpair s)
    have hFD : F.MDifferentiable IR2 (𝓡 2) :=
      ⟨hF.mdifferentiableOn (by simp), hFi.mdifferentiableOn (by simp)⟩
    have hkd : Injective (mfderiv IR (𝓡 2) k s) := by
      change Injective (mfderiv IR (𝓡 2) (F ∘ fun y : Real => (y, t)) s)
      rw [mfderiv_comp s (hFD.mdifferentiableAt hs) (hpair.mdifferentiable (by simp) s)]
      exact (hFD.mfderiv_bijective hs).1.comp hpairder
    have hfull : Injective (fderiv Real (g ∘ k) s) := by
      rw [← mfderiv_eq_fderiv,
        mfderiv_comp s (hg.mdifferentiable (by simp) (k s)) (hk.mdifferentiableAt (by simp))]
      exact (hgd (k s)).comp hkd
    let q : Real → E2 := fun y => toE2 (G (F (y, t)))
    have hqcont : ContDiffAt Real ∞ q s :=
      (contDiff_toE2.contMDiff.contMDiffAt.comp s (hg.contMDiffAt.comp s hk)).contDiffAt
    have hq : DifferentiableAt Real q s := hqcont.differentiableAt (by simp)
    have hnear : ∀ᶠ y in 𝓝 s, (y, t) ∈ F.source :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (F.open_source.mem_nhds hs)
    have heq : g ∘ k =ᶠ[𝓝 s] (fun y => toE3 (q y) (H t)) := by
      filter_upwards [hnear] with y hy
      ext i
      fin_cases i
      · rfl
      · rfl
      · exact hheight (y, t) hy
    have hd : HasDerivAt (fun y => toE3 (q y) (H t))
        (fderiv Real (fun x => toE3 x (H t)) (q s) (deriv q s)) s :=
      (((contDiff_toE3 (H t)).differentiable (by simp) (q s)).hasFDerivAt).comp_hasDerivAt
        s hq.hasDerivAt
    intro hz
    have hzero : deriv (g ∘ k) s = 0 := by
      rw [heq.deriv_eq, hd.deriv]
      change (fderiv Real (fun x => toE3 x (H t)) (q s)) (deriv q s) = 0
      rw [show deriv q s = 0 from hz, map_zero]
    have h10 : (1 : Real) = 0 := hfull (by
      simpa only [map_zero, fderiv_apply_one_eq_deriv] using hzero)
    exact one_ne_zero h10

private theorem exists_reparametrized_interval_geometry
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {l u η ε : Real} (hη : 0 < η) (hε : 0 < ε)
    (μ : Real × Real → E) {W : Set (Real × Real)} (hW : IsOpen W)
    (hrect : Icc (-η) η ×ˢ Icc (l - ε) (u + ε) ⊆ W)
    (hμ : ContDiffOn Real ∞ μ W)
    (hμinj : ∀ t ∈ Icc (-η) η,
      InjOn (fun s => μ (t, s)) (Icc (l - ε) (u + ε)))
    (hμder : ∀ t ∈ Icc (-η) η, ∀ s ∈ Icc (l - ε) (u + ε),
      deriv (fun y => μ (t, y)) s ≠ 0)
    (R : Real → Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞)
    (hR : ContDiff Real ∞ (fun z : Real × Real => R z.1 z.2))
    (hRzero : ∀ s, R 0 s = s) :
    let ν : Real × Real → E := fun z => μ (z.1, R z.1 z.2)
    ∃ δ : Real, 0 < δ ∧ δ < η ∧ ∃ W' : Set (Real × Real),
      IsOpen W' ∧ Icc (-δ) δ ×ˢ Icc l u ⊆ W' ∧
      ContDiffOn Real ∞ ν W' ∧
      (∀ t ∈ Icc (-δ) δ, InjOn (fun s => ν (t, s)) (Icc l u)) ∧
      (∀ t ∈ Icc (-δ) δ, ∀ s ∈ Icc l u,
        deriv (fun y => ν (t, y)) s ≠ 0) ∧
      (∀ s, ν (0, s) = μ (0, s)) ∧
      ∀ t ∈ Icc (-δ) δ, ∀ s ∈ Icc l u, R t s ∈ Ioo (l - ε) (u + ε) := by
  dsimp only
  have hevent : ∀ᶠ t in 𝓝 (0 : Real), ∀ s ∈ Icc l u,
      R t s ∈ Ioo (l - ε) (u + ε) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    apply hR.continuous.continuousAt.eventually
    apply isOpen_Ioo.mem_nhds
    change R 0 s ∈ Ioo (l - ε) (u + ε)
    rw [hRzero s]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨ρ, hρ, hρrange⟩ := Metric.mem_nhds_iff.mp hevent
  let δ := min (η / 2) (ρ / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδη : δ < η := (min_le_left _ _).trans_lt (by linarith)
  have htime (t : Real) (ht : t ∈ Icc (-δ) δ) : t ∈ Icc (-η) η :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hrange (t : Real) (ht : t ∈ Icc (-δ) δ) (s : Real) (hs : s ∈ Icc l u) :
      R t s ∈ Ioo (l - ε) (u + ε) := by
    apply hρrange (show t ∈ ball (0 : Real) ρ from ?_) s hs
    have hdρ := min_le_right (η / 2) (ρ / 2)
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let T : Real × Real → Real × Real := fun z => (z.1, R z.1 z.2)
  have hT : ContDiff Real ∞ T := contDiff_fst.prodMk hR
  let W' : Set (Real × Real) := T ⁻¹' W
  have hW' : IsOpen W' := hW.preimage hT.continuous
  have hν : ContDiffOn Real ∞ (fun z => μ (z.1, R z.1 z.2)) W' :=
    hμ.comp hT.contDiffOn (fun _ hz => hz)
  refine ⟨δ, hδ, hδη, W', hW', ?_, hν, ?_, ?_, ?_, hrange⟩
  · intro z hz
    exact hrect ⟨htime z.1 hz.1, Ioo_subset_Icc_self (hrange z.1 hz.1 z.2 hz.2)⟩
  · intro t ht s hs y hy heq
    apply (R t).injective
    exact hμinj t (htime t ht)
      (Ioo_subset_Icc_self (hrange t ht s hs))
      (Ioo_subset_Icc_self (hrange t ht y hy)) heq
  · intro t ht s hs
    have hRsm : DifferentiableAt Real (R t) s := (R t).contDiff.differentiable (by simp) s
    have hμsm : DifferentiableAt Real (fun y => μ (t, y)) (R t s) :=
      ((hμ.contDiffAt (hW.mem_nhds
        (hrect ⟨htime t ht, Ioo_subset_Icc_self (hrange t ht s hs)⟩))).comp (R t s)
        ((contDiff_const.prodMk contDiff_id).contDiffAt)).differentiableAt (by simp)
    have hd : HasDerivAt (fun y => μ (t, R t y))
        (deriv (R t) s • deriv (fun y => μ (t, y)) (R t s)) s :=
      hμsm.hasDerivAt.scomp s hRsm.hasDerivAt
    rw [hd.deriv]
    exact smul_ne_zero
      (Poincare.Manifold.Schoenflies.deriv_real_diffeomorph_ne_zero (R t) s)
      (hμder t (htime t ht) (R t s) (Ioo_subset_Icc_self (hrange t ht s hs)))
  · intro s
    rw [hRzero s]

private theorem exists_stationary_regular_planar_strip
    (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (p₀ : S2)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) 𝓘(Real, Real × Real) ∞ F.symm F.target)
    (hheight : ∀ z ∈ F.source, G (F z) 2 = z.2)
    (l l₁ u₁ u : Real) {ε : Real} (hε : 0 < ε)
    (hFcentral : ∀ s ∈ Icc (l - ε) (u + ε), (s, 0) ∈ F.source)
    (g : S2 → E3) (U : Set E3)
    (hcommon : (G '' sphere (0 : E3) 1) ∩ U = range g ∩ U)
    (y : Real × Real → E3) {W : Set (Real × Real)} (hW : IsOpen W)
    (hy : ContDiffOn Real ∞ y W)
    (hyactual : MapsTo y W (range g)) (hyU : MapsTo y W U)
    (hyheight : ∀ z ∈ W, y z 2 = z.1)
    (hyvertical : ∀ z ∈ W, toE2 (y z) = toE2 (y (0, z.2)))
    (χ : Real → Real) (hχ : ContDiff Real ∞ χ) (hχc : HasCompactSupport χ)
    (hχends : ∀ s ∈ Icc l l₁ ∪ Icc u₁ u, χ s = 1)
    (hWzero : ∀ s ∈ tsupport χ, (0, s) ∈ W)
    (hsource : ∀ s ∈ tsupport χ, (s, 0) ∈ F.source)
    (hcentral : ∀ s ∈ tsupport χ, y (0, s) = G (F (s, 0))) :
    ∃ δ : Real, 0 < δ ∧
      ∃ R : Real → Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞,
        (∀ s, R 0 s = s) ∧
        ContDiff Real ∞ (fun z : Real × Real => R z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × Real => (R z.1).symm z.2) ∧
        (∀ t s, s ∉ tsupport χ → R t s = s) ∧
        let μ : Real × Real → E2 := fun z => toE2 (G (F (R z.1 z.2, z.1)))
        ∃ V : Set (Real × Real), IsOpen V ∧ Icc (-δ) δ ×ˢ Icc l u ⊆ V ∧
          ContDiffOn Real ∞ μ V ∧
          (∀ t ∈ Icc (-δ) δ, InjOn (fun s => μ (t, s)) (Icc l u)) ∧
          (∀ t ∈ Icc (-δ) δ, ∀ s ∈ Icc l u,
            deriv (fun a => μ (t, a)) s ≠ 0) ∧
          (∀ s, μ (0, s) = toE2 (G (F (s, 0)))) ∧
          (∀ t ∈ Icc (-δ) δ, ∀ s ∈ Icc l u, (R t s, t) ∈ F.source) ∧
          (∀ t ∈ Icc (-δ) δ, ∀ s ∈ Icc l l₁ ∪ Icc u₁ u,
            μ (t, s) = μ (0, s)) ∧
          ∀ t ∈ Icc (-δ) δ, ∀ s ∈ Icc l l₁ ∪ Icc u₁ u,
            G (F (R t s, t)) = y (t, s) := by
  obtain ⟨r, hr, R, hRzero, hR, hRinv, hRfix, hRmatch⟩ :=
    exists_stationary_model_strip_coordinates
      G p₀ F hFi hheight g U hcommon y hW hy hyactual hyU hyheight hyvertical
      χ hχ hχc hWzero hsource hcentral
  have hevent : ∀ᶠ t in 𝓝 (0 : Real), ∀ s ∈ Icc (l - ε) (u + ε),
      (s, t) ∈ F.source := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    apply (continuous_snd.prodMk continuous_fst).continuousAt.eventually
    exact F.open_source.mem_nhds (hFcentral s hs)
  obtain ⟨ρ, hρ, hρrange⟩ := Metric.mem_nhds_iff.mp hevent
  let η : Real := ρ / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hrect : Icc (-η) η ×ˢ Icc (l - ε) (u + ε) ⊆ Prod.swap ⁻¹' F.source := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    apply hρrange (show t ∈ ball (0 : Real) ρ from ?_) s hs
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
    dsimp [η] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨hμ, hinj, hder⟩ := planar_strip_geometry G F hF hFi id hheight
  obtain ⟨d, hd, hdη, V, hV, hVrect, hν, hνinj, hνder, hνzero, hrange⟩ :=
    exists_reparametrized_interval_geometry hη hε
      (fun z : Real × Real => toE2 (G (F (z.2, z.1))))
      (F.open_source.preimage continuous_swap) hrect hμ
      (fun t ht => (hinj t).mono (fun s hs => hrect
        (show (t, s) ∈ Icc (-η) η ×ˢ Icc (l - ε) (u + ε) from ⟨ht, hs⟩)))
      (fun t ht s hs => hder t s (hrect
        (show (t, s) ∈ Icc (-η) η ×ˢ Icc (l - ε) (u + ε) from ⟨ht, hs⟩))) R hR hRzero
  let δ := min d r
  have hδ : 0 < δ := lt_min hd hr
  have hδd : δ ≤ d := min_le_left _ _
  have hδr : δ ≤ r := min_le_right _ _
  have htime {t : Real} (ht : t ∈ Icc (-δ) δ) : t ∈ Icc (-d) d :=
    ⟨by linarith [ht.1], ht.2.trans hδd⟩
  have htimer {t : Real} (ht : t ∈ Icc (-δ) δ) : t ∈ Icc (-r) r :=
    ⟨by linarith [ht.1], ht.2.trans hδr⟩
  refine ⟨δ, hδ, R, hRzero, hR, hRinv, hRfix, V, hV, ?_, hν,
    fun t ht => hνinj t (htime ht), fun t ht => hνder t (htime ht), hνzero, ?_, ?_, ?_⟩
  · intro z hz
    exact hVrect ⟨htime hz.1, hz.2⟩
  · intro t ht s hs
    change (t, R t s) ∈ Prod.swap ⁻¹' F.source
    apply hrect
    refine ⟨?_, Ioo_subset_Icc_self (hrange t (htime ht) s hs)⟩
    exact ⟨by linarith [(htime ht).1], (htime ht).2.trans hdη.le⟩
  · intro t ht s hs
    simpa only [hRzero] using (hRmatch t (htimer ht) s (hχends s hs)).2
  · intro t ht s hs
    exact (hRmatch t (htimer ht) s (hχends s hs)).1

theorem flattened_exterior_eq_projected_model_strips
    (T D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (p : S2) (d : OpenPartialHomeomorph E2 S2)
    {s c u r : Real} (hs : 0 < s)
    (hheight : ∀ q : S2, D (T (shear (3 / 10) q)) 2 =
      c + s * (height q - height p))
    (F : Fin 2 → Real × Real → S2) (A B : Fin 2 → Real)
    (hrecut : (height ⁻¹' {height p + u}) \ d '' openSquare r =
      ⋃ i, F i '' (Icc (A i) (B i) ×ˢ ({u} : Set Real))) :
    (⋃ i, (fun z => toE2 (D (T (shear (3 / 10) (F i (z, u)))))) ''
      Icc (A i) (B i)) =
      {x | polynomial (3 / 10) (T.symm (D.symm (toE3 x (c + s * u)))) = 1 ∧
        toE3 x (c + s * u) ∉
          (fun q : S2 => D (T (shear (3 / 10) q))) '' (d '' openSquare r)} := by
  let g : S2 → E3 := fun q => D (T (shear (3 / 10) q))
  have hgi : Injective g :=
    D.injective.comp (T.injective.comp ((shear (3 / 10)).injective.comp Subtype.val_injective))
  have hfiber : g '' (height ⁻¹' {height p + u}) =
      (D '' (T '' (shear (3 / 10) '' sphere (0 : E3) 1))) ∩
        {y | y 2 = c + s * u} := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨⟨_, ⟨_, ⟨q, q.property, rfl⟩, rfl⟩, rfl⟩, ?_⟩
      change D (T (shear (3 / 10) q)) 2 = c + s * u
      rw [hheight, show height q = height p + u from hq]
      ring
    · rintro ⟨⟨_, ⟨_, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩, ht⟩
      refine ⟨⟨q, hq⟩, ?_, rfl⟩
      change height ⟨q, hq⟩ = height p + u
      have hh := hheight ⟨q, hq⟩
      change D (T (shear (3 / 10) q)) 2 = c + s * u at ht
      rw [ht] at hh
      nlinarith
  have hspatial : g '' ((height ⁻¹' {height p + u}) \ d '' openSquare r) =
      slice {x | polynomial (3 / 10) (T.symm (D.symm (toE3 x (c + s * u)))) = 1 ∧
        toE3 x (c + s * u) ∉ g '' (d '' openSquare r)} (c + s * u) := by
    rw [image_sdiff hgi, hfiber, flattened_exterior_level_eq]
  have hproject (S : Set E2) (t : Real) : toE2 '' slice S t = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy.1
    · intro hx
      have hcoord : toE2 (toE3 x t) = x := by ext i; fin_cases i <;> rfl
      refine ⟨toE3 x t, ⟨?_, rfl⟩, hcoord⟩
      simpa only [hcoord] using hx
  have heq := congrArg (fun S => toE2 '' S) hspatial
  rw [hproject, hrecut, image_iUnion, image_iUnion] at heq
  rw [← heq]
  apply iUnion_congr
  intro i
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨g (F i (z, u)), ⟨F i (z, u), ⟨(z, u), ⟨hz, rfl⟩, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨_, ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩, rfl⟩, rfl⟩
    have htu : t = u := ht
    subst t
    exact ⟨z, hz, rfl⟩

end ModelStrips

section ModelConstruction

open SaddleLevel Filter
open scoped _root_.Topology
set_option backward.isDefEq.respectTransparency false

private theorem exists_central_strip_germ_of_common_surface
    (g : S2 → E3) (hg : Continuous g) (hginj : Function.Injective g)
    {Z U : Set E3} (hU : IsOpen U)
    (hcommon : range g ∩ U = Z ∩ U)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    {a b eta : Real} (heta : 0 < eta)
    (hsource : Ioo a b ×ˢ Ioo (-eta) eta ⊆ F.source)
    (hheight : ∀ z ∈ Ioo a b ×ˢ Ioo (-eta) eta, g (F z) 2 = z.2)
    (gamma : Real → E3) {N₀ : Set Real} (hN₀ : IsOpen N₀)
    (hgamma : ContinuousOn gamma N₀)
    (hgammaZ : MapsTo gamma N₀ Z)
    (hgamma_height : ∀ s ∈ N₀, gamma s 2 = 0)
    {s₀ a₀ : Real} (hs₀ : s₀ ∈ N₀) (ha₀ : a₀ ∈ Ioo a b)
    (hcontact : gamma s₀ = g (F (a₀, 0))) (hcontactU : gamma s₀ ∈ U) :
    ∃ N : Set Real, IsOpen N ∧ s₀ ∈ N ∧ N ⊆ N₀ ∧
      gamma '' N ⊆ (fun s => g (F (s, 0))) '' Ioo a b ∧ gamma '' N ⊆ U := by
  let R : Set (Real × Real) := Ioo a b ×ˢ Ioo (-eta) eta
  let V : Set S2 := F '' R
  have hV : IsOpen V := F.isOpen_image_of_subset_source
    (isOpen_Ioo.prod isOpen_Ioo) hsource
  have hclosed : IsClosed (g '' Vᶜ) := (hV.isClosed_compl.isCompact.image hg).isClosed
  let O : Set E3 := U ∩ (g '' Vᶜ)ᶜ
  have hO : IsOpen O := hU.inter hclosed.isOpen_compl
  have hcontactO : gamma s₀ ∈ O := by
    refine ⟨hcontactU, ?_⟩
    rintro ⟨q, hq, heq⟩
    rw [hcontact] at heq
    have hqeq : q = F (a₀, 0) := hginj heq
    apply hq
    rw [hqeq]
    exact ⟨(a₀, 0), ⟨ha₀, by constructor <;> linarith⟩, rfl⟩
  let N : Set Real := N₀ ∩ gamma ⁻¹' O
  refine ⟨N, hgamma.isOpen_inter_preimage hN₀ hO,
    ⟨hs₀, hcontactO⟩, inter_subset_left, ?_, ?_⟩
  · rintro y ⟨s, hs, rfl⟩
    have hactual : gamma s ∈ range g ∩ U := by
      rw [hcommon]
      exact ⟨hgammaZ hs.1, hs.2.1⟩
    obtain ⟨q, hq⟩ := hactual.1
    have hqV : q ∈ V := by
      by_contra hn
      exact hs.2.2 ⟨q, hn, hq⟩
    obtain ⟨⟨u, t⟩, hut, rfl⟩ := hqV
    have ht : t = 0 := by
      calc
        t = g (F (u, t)) 2 := (hheight (u, t) hut).symm
        _ = gamma s 2 := congrArg (fun y : E3 => y 2) hq
        _ = 0 := hgamma_height s hs.1
    subst t
    exact ⟨u, hut.1, hq⟩
  · rintro y ⟨s, hs, rfl⟩
    exact hs.2.1

private theorem exists_common_central_strip_germs
    (g : S2 → E3) (hg : Continuous g) (hginj : Function.Injective g)
    {Z U : Set E3} (hU : IsOpen U) (hcommon : range g ∩ U = Z ∩ U)
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
    (a b : Fin 2 → Real) {eta : Real} (heta : 0 < eta)
    (hsource : ∀ i, Ioo (a i) (b i) ×ˢ Ioo (-eta) eta ⊆ (F i).source)
    (hheight : ∀ i z, z ∈ Ioo (a i) (b i) ×ˢ Ioo (-eta) eta →
      g (F i z) 2 = z.2)
    (gamma : Real → E3) {l a₀ b₀ u : Real}
    (hla₀ : l < a₀) (ha₀b₀ : a₀ < b₀) (hb₀u : b₀ < u)
    (hgamma : ContinuousOn gamma (Ioo l u))
    (hgammaZ : MapsTo gamma (Ioo l u) Z)
    (hgamma_height : ∀ s ∈ Ioo l u, gamma s 2 = 0)
    (j₀ j₁ : Fin 2) (q₀ q₁ : Real)
    (hq₀ : q₀ ∈ Ioo (a j₀) (b j₀)) (hq₁ : q₁ ∈ Ioo (a j₁) (b j₁))
    (hcontact₀ : gamma a₀ = g (F j₀ (q₀, 0)))
    (hcontact₁ : gamma b₀ = g (F j₁ (q₁, 0)))
    (hcontactU₀ : gamma a₀ ∈ U) (hcontactU₁ : gamma b₀ ∈ U) :
    ∃ N : Set Real, IsOpen N ∧ a₀ ∈ N ∧ b₀ ∈ N ∧ N ⊆ Ioo l u ∧
      gamma '' N ⊆ ⋃ i, (fun s => g (F i (s, 0))) '' Icc (a i) (b i) ∧
      gamma '' N ⊆ U := by
  obtain ⟨N₀, hN₀, ha₀N₀, hN₀sub, hN₀image, hN₀U⟩ :=
    exists_central_strip_germ_of_common_surface g hg hginj hU hcommon (F j₀)
      heta (hsource j₀) (hheight j₀) gamma isOpen_Ioo hgamma hgammaZ hgamma_height
      ⟨hla₀, ha₀b₀.trans hb₀u⟩ hq₀ hcontact₀ hcontactU₀
  obtain ⟨N₁, hN₁, hb₀N₁, hN₁sub, hN₁image, hN₁U⟩ :=
    exists_central_strip_germ_of_common_surface g hg hginj hU hcommon (F j₁)
      heta (hsource j₁) (hheight j₁) gamma isOpen_Ioo hgamma hgammaZ hgamma_height
      ⟨hla₀.trans ha₀b₀, hb₀u⟩ hq₁ hcontact₁ hcontactU₁
  refine ⟨N₀ ∪ N₁, hN₀.union hN₁, Or.inl ha₀N₀, Or.inr hb₀N₁,
    union_subset hN₀sub hN₁sub, ?_, ?_⟩
  · rintro y ⟨s, hs, rfl⟩
    rcases hs with hs | hs
    · obtain ⟨q, hq, heq⟩ := hN₀image (mem_image_of_mem gamma hs)
      exact mem_iUnion_of_mem j₀ ⟨q, Ioo_subset_Icc_self hq, heq⟩
    · obtain ⟨q, hq, heq⟩ := hN₁image (mem_image_of_mem gamma hs)
      exact mem_iUnion_of_mem j₁ ⟨q, Ioo_subset_Icc_self hq, heq⟩
  · rintro y ⟨s, hs, rfl⟩
    rcases hs with hs | hs
    · exact hN₀U (mem_image_of_mem gamma hs)
    · exact hN₁U (mem_image_of_mem gamma hs)

private theorem exists_vertical_germ_domain_of_flattened_strips
    {K N : Set Real} (hK : IsCompact K) (hN : IsOpen N) (hKN : K ⊆ N)
    (gamma : Real → E3) (hgamma : ContDiffOn Real ∞ gamma N)
    (hgamma_height : ∀ s ∈ N, gamma s 2 = 0)
    (g : S2 → E3) (F : Fin 2 → Real × Real → S2)
    (a b : Fin 2 → Real) (D : E3 → E3)
    {eta : Real} (heta : 0 < eta)
    (hcover : gamma '' N ⊆
      ⋃ i, (fun s => g (F i (s, 0))) '' Icc (a i) (b i))
    (hflat : ∀ i s, s ∈ Icc (a i) (b i) → ∀ t ∈ Ioo (-eta) eta,
      D (g (F i (s, t))) =
        g (F i (s, 0)) + t • (EuclideanSpace.single 2 1 : E3))
    {U : Set E3} (hU : IsOpen U) (hgammaU : gamma '' K ⊆ U) :
    let y : Real × Real → E3 :=
      fun z => gamma z.2 + z.1 • (EuclideanSpace.single 2 1 : E3)
    ∃ (delta : Real) (W : Set (Real × Real)),
      0 < delta ∧ delta < eta ∧ IsOpen W ∧ Icc (-delta) delta ×ˢ K ⊆ W ∧
      W ⊆ Ioo (-eta) eta ×ˢ N ∧
      ContDiffOn Real ∞ y W ∧ MapsTo y W (range (D ∘ g) ∩ U) ∧
      (∀ z ∈ W, y z 2 = z.1) ∧
      (∀ z ∈ W, Saddle.toE2 (y z) = Saddle.toE2 (gamma z.2)) ∧
      (∀ z ∈ W, Saddle.toE2 (y z) = Saddle.toE2 (y (0, z.2))) := by
  let y : Real × Real → E3 :=
    fun z => gamma z.2 + z.1 • (EuclideanSpace.single 2 1 : E3)
  change ∃ (delta : Real) (W : Set (Real × Real)), _
  let B : Set (Real × Real) := Ioo (-eta) eta ×ˢ N
  have hB : IsOpen B := isOpen_Ioo.prod hN
  have hy : ContDiffOn Real ∞ y B :=
    (hgamma.comp contDiff_snd.contDiffOn (fun _ hz => hz.2)).add
      (contDiff_fst.smul contDiff_const).contDiffOn
  let W : Set (Real × Real) := B ∩ y ⁻¹' U
  have hW : IsOpen W := hy.continuousOn.isOpen_inter_preimage hB hU
  have hcentral : ({0} : Set Real) ×ˢ K ⊆ W := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have ht0 : t = 0 := ht
    subst t
    exact ⟨⟨⟨by linarith, heta⟩, hKN hs⟩,
      by simpa [y] using hgammaU (mem_image_of_mem gamma hs)⟩
  obtain ⟨V, O, hV, _, h0V, hKO, hVO⟩ :=
    generalized_tube_lemma isCompact_singleton hK hW hcentral
  obtain ⟨l, u, hlu, hinterval⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hV.mem_nhds (h0V rfl))
  let delta : Real := min eta (min (-l) u) / 2
  have hmin : 0 < min eta (min (-l) u) :=
    lt_min heta (lt_min (by linarith [hlu.1]) hlu.2)
  have hdelta : 0 < delta := half_pos hmin
  have hdeta : delta < eta := (half_lt_self hmin).trans_le (min_le_left _ _)
  have hdl : delta < -l := (half_lt_self hmin).trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hdu : delta < u := (half_lt_self hmin).trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  have hrect : Icc (-delta) delta ×ˢ K ⊆ W := by
    intro z hz
    exact hVO ⟨hinterval ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hKO hz.2⟩
  have hvertical (z : Real × Real) :
      Saddle.toE2 (y z) = Saddle.toE2 (gamma z.2) := by
    ext i
    fin_cases i <;> simp [Saddle.toE2, y]
  refine ⟨delta, W, hdelta, hdeta, hW, hrect, inter_subset_left,
    hy.mono inter_subset_left, ?_, ?_, fun z _ => hvertical z, ?_⟩
  · intro z hz
    refine ⟨?_, hz.2⟩
    obtain ⟨i, s, hs, heq⟩ := mem_iUnion.mp
      (hcover (mem_image_of_mem gamma hz.1.2))
    change g (F i (s, 0)) = gamma z.2 at heq
    refine ⟨F i (s, z.1), ?_⟩
    change D (g (F i (s, z.1))) = gamma z.2 + z.1 • _
    rw [hflat i s hs z.1 hz.1.1, heq]
  · intro z hz
    simp [hgamma_height z.2 hz.1.2]
  · intro z hz
    simpa [y] using hvertical z

private theorem exists_endpoint_collars_and_cutoff
    {a a₀ b₀ b : Real} (haa₀ : a < a₀) (ha₀b₀ : a₀ < b₀) (hb₀b : b₀ < b)
    {N : Set Real} (hN : IsOpen N) (ha₀N : a₀ ∈ N) (hb₀N : b₀ ∈ N) :
    ∃ (l l₀ l₁ u₁ u₀ u : Real) (χ : Real → Real),
      (a < l ∧ l < l₀ ∧ l₀ < a₀ ∧ a₀ < l₁ ∧ l₁ < u₁ ∧
        u₁ < b₀ ∧ b₀ < u₀ ∧ u₀ < u ∧ u < b) ∧
      Icc l l₁ ∪ Icc u₁ u ⊆ N ∧
      ContDiff Real ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ N ∩ Ioo a b ∧
      (∀ s, χ s ∈ Icc 0 1) ∧
      (∀ s ∈ Icc l l₁ ∪ Icc u₁ u, χ s = 1) := by
  let m : Real := (a₀ + b₀) / 2
  have ha₀m : a₀ < m := by dsimp [m]; linarith
  have hmb₀ : m < b₀ := by dsimp [m]; linarith
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp
    ((hN.inter isOpen_Ioo).mem_nhds
      (show a₀ ∈ N ∩ Ioo a m from ⟨ha₀N, haa₀, ha₀m⟩))
  obtain ⟨q, hq, hqsub⟩ := Metric.mem_nhds_iff.mp
    ((hN.inter isOpen_Ioo).mem_nhds
      (show b₀ ∈ N ∩ Ioo m b from ⟨hb₀N, hmb₀, hb₀b⟩))
  let l : Real := a₀ - r / 2
  let l₀ : Real := a₀ - r / 4
  let l₁ : Real := a₀ + r / 2
  let u₁ : Real := b₀ - q / 2
  let u₀ : Real := b₀ + q / 4
  let u : Real := b₀ + q / 2
  have hleft : Icc l l₁ ⊆ N ∩ Ioo a m := by
    intro s hs
    apply hrsub
    rw [mem_ball, Real.dist_eq, abs_lt]
    dsimp [l, l₁] at hs
    constructor <;> linarith [hs.1, hs.2]
  have hright : Icc u₁ u ⊆ N ∩ Ioo m b := by
    intro s hs
    apply hqsub
    rw [mem_ball, Real.dist_eq, abs_lt]
    dsimp [u₁, u] at hs
    constructor <;> linarith [hs.1, hs.2]
  have hll₁ : l ≤ l₁ := by dsimp [l, l₁]; linarith
  have hu₁u : u₁ ≤ u := by dsimp [u₁, u]; linarith
  have hl : a < l := (hleft ⟨le_rfl, hll₁⟩).2.1
  have hl₁ : l₁ < m := (hleft ⟨hll₁, le_rfl⟩).2.2
  have hu₁ : m < u₁ := (hright ⟨le_rfl, hu₁u⟩).2.1
  have hu : u < b := (hright ⟨hu₁u, le_rfl⟩).2.2
  let K : Set Real := Icc l l₁ ∪ Icc u₁ u
  have hK : IsCompact K := isCompact_Icc.union isCompact_Icc
  have hKU : K ⊆ N ∩ Ioo a b := by
    intro s hs
    rcases hs with hs | hs
    · obtain ⟨hsN, hsa, hsm⟩ := hleft hs
      exact ⟨hsN, hsa, hsm.trans (hmb₀.trans hb₀b)⟩
    · obtain ⟨hsN, hms, hsb⟩ := hright hs
      exact ⟨hsN, (haa₀.trans ha₀m).trans hms, hsb⟩
  obtain ⟨χ, hχ, hχcompact, hχsupport, hχrange, hχone, _⟩ :=
    Poincare.Manifold.exists_compact_smooth_cutoff 𝓘(Real, Real)
      hK (hN.inter isOpen_Ioo) hKU
  refine ⟨l, l₀, l₁, u₁, u₀, u, χ, ?_,
    hKU.trans inter_subset_left, hχ.contDiff, hχcompact, hχsupport, hχrange, ?_⟩
  · refine ⟨hl, ?_, ?_, ?_, hl₁.trans hu₁, ?_, ?_, ?_, hu⟩ <;>
      dsimp [l, l₀, l₁, u₁, u₀, u] <;> linarith
  · intro s hs
    exact hχone.self_of_nhdsSet s hs

private theorem exists_endpoint_cutoff_and_vertical_germ
    (g : S2 → E3) (hg : Continuous g) (hginj : Function.Injective g)
    {Z U : Set E3} (hU : IsOpen U) (hcommon : range g ∩ U = Z ∩ U)
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
    (a b : Fin 2 → Real) {eta : Real} (heta : 0 < eta)
    (hsource : ∀ i, Ioo (a i) (b i) ×ˢ Ioo (-eta) eta ⊆ (F i).source)
    (hheight : ∀ i z, z ∈ Ioo (a i) (b i) ×ˢ Ioo (-eta) eta →
      g (F i z) 2 = z.2)
    (gamma : Real → E3) {v a₀ b₀ w : Real}
    (hva₀ : v < a₀) (ha₀b₀ : a₀ < b₀) (hb₀w : b₀ < w)
    (hgamma : ContDiffOn Real ∞ gamma (Ioo v w))
    (hgammaZ : MapsTo gamma (Ioo v w) Z)
    (hgamma_height : ∀ s ∈ Ioo v w, gamma s 2 = 0)
    (j₀ j₁ : Fin 2) (q₀ q₁ : Real)
    (hq₀ : q₀ ∈ Ioo (a j₀) (b j₀)) (hq₁ : q₁ ∈ Ioo (a j₁) (b j₁))
    (hcontact₀ : gamma a₀ = g (F j₀ (q₀, 0)))
    (hcontact₁ : gamma b₀ = g (F j₁ (q₁, 0)))
    (hcontactU₀ : gamma a₀ ∈ U) (hcontactU₁ : gamma b₀ ∈ U)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDzero : ∀ x : E3, x 2 = 0 → D x = x)
    (hflat : ∀ i s, s ∈ Icc (a i) (b i) → ∀ t ∈ Ioo (-eta) eta,
      D (g (F i (s, t))) =
        g (F i (s, 0)) + t • (EuclideanSpace.single 2 1 : E3)) :
    let y : Real × Real → E3 :=
      fun z => gamma z.2 + z.1 • (EuclideanSpace.single 2 1 : E3)
    ∃ (N : Set Real) (l l₀ l₁ u₁ u₀ u : Real) (χ : Real → Real)
        (delta : Real) (W : Set (Real × Real)),
      IsOpen N ∧ a₀ ∈ N ∧ b₀ ∈ N ∧ N ⊆ Ioo v w ∧
      (gamma '' N ⊆ ⋃ i, (fun s => g (F i (s, 0))) '' Icc (a i) (b i)) ∧
      gamma '' N ⊆ U ∧
      (v < l ∧ l < l₀ ∧ l₀ < a₀ ∧ a₀ < l₁ ∧ l₁ < u₁ ∧
        u₁ < b₀ ∧ b₀ < u₀ ∧ u₀ < u ∧ u < w) ∧
      Icc l l₁ ∪ Icc u₁ u ⊆ N ∧
      ContDiff Real ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ N ∩ Ioo v w ∧
      (∀ s, χ s ∈ Icc 0 1) ∧
      (∀ s ∈ Icc l l₁ ∪ Icc u₁ u, χ s = 1) ∧
      0 < delta ∧ delta < eta ∧ IsOpen W ∧
      Icc (-delta) delta ×ˢ tsupport χ ⊆ W ∧ W ⊆ Ioo (-eta) eta ×ˢ N ∧
      ContDiffOn Real ∞ y W ∧ MapsTo y W (range (D ∘ g) ∩ (D '' U)) ∧
      (∀ z ∈ W, y z 2 = z.1) ∧
      (∀ z ∈ W, Saddle.toE2 (y z) = Saddle.toE2 (y (0, z.2))) := by
  obtain ⟨N, hN, ha₀N, hb₀N, hNsub, hNcover, hNU⟩ :=
    exists_common_central_strip_germs g hg hginj hU hcommon F a b heta
      hsource hheight gamma hva₀ ha₀b₀ hb₀w hgamma.continuousOn hgammaZ
      hgamma_height j₀ j₁ q₀ q₁ hq₀ hq₁ hcontact₀ hcontact₁ hcontactU₀ hcontactU₁
  obtain ⟨l, l₀, l₁, u₁, u₀, u, χ, hchain, hends, hχ, hχcompact,
      hχsupport, hχrange, hχone⟩ :=
    exists_endpoint_collars_and_cutoff hva₀ ha₀b₀ hb₀w hN ha₀N hb₀N
  have hDU : IsOpen (D '' U) := D.toHomeomorph.isOpenMap U hU
  have hcentralDU : gamma '' tsupport χ ⊆ D '' U := by
    rintro x ⟨s, hs, rfl⟩
    exact ⟨gamma s, hNU (mem_image_of_mem gamma (hχsupport hs).1),
      hDzero _ (hgamma_height s (hχsupport hs).2)⟩
  obtain ⟨delta, W, hdelta, hdeta, hW, hrect, hWsub, hy, hyactual,
      hyheight, _, hyvertical⟩ :=
    exists_vertical_germ_domain_of_flattened_strips hχcompact.isCompact hN
      (fun s hs => (hχsupport hs).1) gamma (hgamma.mono hNsub)
      (fun s hs => hgamma_height s (hNsub hs)) g (fun i z => F i z) a b D heta
      hNcover hflat hDU hcentralDU
  exact ⟨N, l, l₀, l₁, u₁, u₀, u, χ, delta, W, hN, ha₀N, hb₀N,
    hNsub, hNcover, hNU, hchain, hends, hχ, hχcompact, hχsupport, hχrange,
    hχone, hdelta, hdeta, hW, hrect, hWsub, hy, hyactual, hyheight, hyvertical⟩

private def stripHeightScale {s : Real} (hs : s ≠ 0) :
    (Real × Real) ≃L[Real] (Real × Real) :=
  (ContinuousLinearEquiv.refl Real Real).prodCongr
    (LinearEquiv.smulOfNeZero Real Real s⁻¹ (inv_ne_zero hs)).toContinuousLinearEquiv

private theorem stripHeightScale_apply {s : Real} (hs : s ≠ 0) (z : Real × Real) :
    stripHeightScale hs z = (z.1, z.2 / s) := by
  change (z.1, s⁻¹ • z.2) = _
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

private theorem stripHeightScale_symm_apply {s : Real} (hs : s ≠ 0) (z : Real × Real) :
    (stripHeightScale hs).symm z = (z.1, s * z.2) := by
  apply (stripHeightScale hs).injective
  rw [(stripHeightScale hs).apply_symm_apply, stripHeightScale_apply]
  simp [hs]

private def physicalHeightStrip {s : Real} (hs : s ≠ 0)
    (F : OpenPartialHomeomorph (Real × Real) S2) :
    OpenPartialHomeomorph (Real × Real) S2 :=
  (stripHeightScale hs).toHomeomorph.toOpenPartialHomeomorph.trans F

private theorem physicalHeightStrip_apply {s : Real} (hs : s ≠ 0)
    (F : OpenPartialHomeomorph (Real × Real) S2) (z : Real × Real) :
    physicalHeightStrip hs F z = F (z.1, z.2 / s) := by
  change F (stripHeightScale hs z) = _
  rw [stripHeightScale_apply]

private theorem physicalHeightStrip_symm_apply {s : Real} (hs : s ≠ 0)
    (F : OpenPartialHomeomorph (Real × Real) S2) (p : S2) :
    (physicalHeightStrip hs F).symm p = ((F.symm p).1, s * (F.symm p).2) := by
  change (stripHeightScale hs).symm (F.symm p) = _
  rw [stripHeightScale_symm_apply]

private theorem physicalHeightStrip_source {s : Real} (hs : s ≠ 0)
    (F : OpenPartialHomeomorph (Real × Real) S2) :
    (physicalHeightStrip hs F).source = {z | (z.1, z.2 / s) ∈ F.source} := by
  ext z
  simp only [physicalHeightStrip, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, mem_inter_iff, mem_univ, mem_preimage,
    true_and, mem_ofPred_eq]
  change stripHeightScale hs z ∈ F.source ↔ _
  rw [stripHeightScale_apply]

private theorem physicalHeightStrip_target {s : Real} (hs : s ≠ 0)
    (F : OpenPartialHomeomorph (Real × Real) S2) :
    (physicalHeightStrip hs F).target = F.target := by
  simp only [physicalHeightStrip, OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target, preimage_univ, inter_univ]

private theorem physicalHeightStrip_smooth {s : Real} (hs : s ≠ 0)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) (𝓡 2) ∞ F F.source) :
    ContMDiffOn 𝓘(Real, Real × Real) (𝓡 2) ∞
      (physicalHeightStrip hs F) (physicalHeightStrip hs F).source := by
  exact hF.comp (stripHeightScale hs).contDiff.contMDiff.contMDiffOn
    (fun _ hz => hz.2)

private theorem physicalHeightStrip_symm_smooth {s : Real} (hs : s ≠ 0)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (hFi : ContMDiffOn (𝓡 2) 𝓘(Real, Real × Real) ∞ F.symm F.target) :
    ContMDiffOn (𝓡 2) 𝓘(Real, Real × Real) ∞
      (physicalHeightStrip hs F).symm (physicalHeightStrip hs F).target := by
  rw [physicalHeightStrip_target]
  exact (stripHeightScale hs).symm.contDiff.contMDiff.comp_contMDiffOn hFi

private theorem physicalHeightStrip_height {s : Real} (hs : s ≠ 0)
    (F : OpenPartialHomeomorph (Real × Real) S2) (G : E3 → E3)
    (hheight : ∀ z ∈ F.source, G (F z) 2 = s * z.2) :
    ∀ z ∈ (physicalHeightStrip hs F).source, G (physicalHeightStrip hs F z) 2 = z.2 := by
  intro z hz
  rw [physicalHeightStrip_source] at hz
  rw [physicalHeightStrip_apply, hheight _ hz]
  exact mul_div_cancel₀ z.2 hs

private theorem physicalHeightStrip_central {s : Real} (hs : s ≠ 0)
    (F : OpenPartialHomeomorph (Real × Real) S2) (x : Real) :
    physicalHeightStrip hs F (x, 0) = F (x, 0) := by
  simp only [physicalHeightStrip_apply, zero_div]

private theorem strictMono_of_compactly_supported_injective
    {f : Real → Real} (hf : Continuous f) (hfinj : Function.Injective f)
    {K : Set Real} (hK : IsCompact K) (hfix : ∀ x, x ∉ K → f x = x) :
    StrictMono f := by
  obtain ⟨b, hb⟩ := hK.bddAbove
  have h₁ : b + 1 ∉ K := by
    intro hx
    have := hb hx
    linarith
  have h₂ : b + 2 ∉ K := by
    intro hx
    have := hb hx
    linarith
  rcases hf.strictMono_of_inj hfinj with hmono | hanti
  · exact hmono
  · have hbad := hanti (show b + 1 < b + 2 by linarith)
    rw [hfix _ h₁, hfix _ h₂] at hbad
    linarith

private theorem image_Icc_inverse_endpoints_of_compact_support
    (R : Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞)
    {K : Set Real} (hK : IsCompact K) (hfix : ∀ s, s ∉ K → R s = s)
    (A B : Real) :
    R '' Icc (R.symm A) (R.symm B) = Icc A B := by
  have hmono := strictMono_of_compactly_supported_injective R.continuous R.injective hK hfix
  simpa using R.continuous.image_Icc_of_strictMono hmono
    (a := R.symm A) (b := R.symm B)

private theorem image_reparametrized_Icc_inverse_endpoints
    {E : Type*} (f : Real → E)
    (R : Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞)
    {K : Set Real} (hK : IsCompact K) (hfix : ∀ s, s ∉ K → R s = s)
    (A B : Real) :
    (fun s => f (R s)) '' Icc (R.symm A) (R.symm B) = f '' Icc A B := by
  rw [← image_image, image_Icc_inverse_endpoints_of_compact_support R hK hfix]

private theorem continuousAt_inverse_recut_endpoint
    (R : Real → Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞)
    (hRinv : ContDiff Real ∞ (fun z : Real × Real => (R z.1).symm z.2))
    {A : Real → Real} {t : Real} (hA : ContinuousAt A t) :
    ContinuousAt (fun u => (R u).symm (A u)) t :=
  hRinv.continuous.continuousAt.comp (continuousAt_id.prodMk hA)

private theorem inverse_recut_endpoint_at_zero
    (R : Real → Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞)
    (hRzero : ∀ s, R 0 s = s) (A : Real → Real) :
    (R 0).symm (A 0) = A 0 := by
  exact (hRzero _).symm.trans ((R 0).apply_symm_apply _)

private theorem exists_uniform_inverse_cut_bounds
    {ι : Type*} [Finite ι] {eta : Real} (heta : 0 < eta)
    (l u : ι → Real) (A B : ι → Real → Real)
    (hA : ∀ i, ContinuousAt (A i) 0) (hB : ∀ i, ContinuousAt (B i) 0)
    (hlA : ∀ i, l i < A i 0) (hAB : ∀ i, A i 0 < B i 0)
    (hBu : ∀ i, B i 0 < u i)
    (R : ι → Real → Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞)
    (hRinv : ∀ i, ContDiff Real ∞ (fun z : Real × Real => (R i z.1).symm z.2))
    (hRzero : ∀ i s, R i 0 s = s) :
    ∃ δ : Real, 0 < δ ∧ δ ≤ eta ∧ ∀ t ∈ Icc (-δ) δ, ∀ i,
      l i < (R i t).symm (A i t) ∧
      (R i t).symm (A i t) < (R i t).symm (B i t) ∧
      (R i t).symm (B i t) < u i := by
  have hevent : ∀ᶠ t in 𝓝 (0 : Real), ∀ i,
      l i < (R i t).symm (A i t) ∧
      (R i t).symm (A i t) < (R i t).symm (B i t) ∧
      (R i t).symm (B i t) < u i := by
    apply Filter.eventually_all.mpr
    intro i
    have ha := continuousAt_inverse_recut_endpoint (R i) (hRinv i) (hA i)
    have hb := continuousAt_inverse_recut_endpoint (R i) (hRinv i) (hB i)
    have ha0 := inverse_recut_endpoint_at_zero (R i) (hRzero i) (A i)
    have hb0 := inverse_recut_endpoint_at_zero (R i) (hRzero i) (B i)
    have hleft : ∀ᶠ t in 𝓝 (0 : Real), l i < (R i t).symm (A i t) :=
      continuousAt_const.eventually_lt ha (by simpa only [ha0] using hlA i)
    have hmiddle : ∀ᶠ t in 𝓝 (0 : Real),
        (R i t).symm (A i t) < (R i t).symm (B i t) :=
      ha.eventually_lt hb (by simpa only [ha0, hb0] using hAB i)
    have hright : ∀ᶠ t in 𝓝 (0 : Real), (R i t).symm (B i t) < u i :=
      hb.eventually_lt continuousAt_const (by simpa only [hb0] using hBu i)
    exact hleft.and (hmiddle.and hright)
  obtain ⟨r, hr, hrange⟩ := Metric.mem_nhds_iff.mp hevent
  let δ := min eta (r / 2)
  have hδ : 0 < δ := lt_min heta (by positivity)
  refine ⟨δ, hδ, min_le_left _ _, ?_⟩
  intro t ht
  apply hrange
  rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
  have hdr : δ ≤ r / 2 := min_le_right _ _
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

private theorem sdiff_eq_of_exterior_coverage
    {E : Type*} (L M P C : Set E) (hML : M ⊆ L)
    (hcover : L \ P ⊆ M) (hPC : P ⊆ C) : L \ C = M \ C := by
  apply Subset.antisymm
  · intro x hx
    exact ⟨hcover ⟨hx.1, fun hp => hx.2 (hPC hp)⟩, hx.2⟩
  · intro x hx
    exact ⟨hML hx.1, hx.2⟩

private theorem exists_fixed_trace_exterior_of_moving_cuts
    {ι E : Type*} [Finite ι] {eta : Real} (heta : 0 < eta)
    (l u : ι → Real) (A B : ι → Real → Real)
    (hA : ∀ i, ContinuousAt (A i) 0) (hB : ∀ i, ContinuousAt (B i) 0)
    (hlA : ∀ i, l i < A i 0) (hAB : ∀ i, A i 0 < B i 0)
    (hBu : ∀ i, B i 0 < u i)
    (R : ι → Real → Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞)
    (hRinv : ∀ i, ContDiff Real ∞ (fun z : Real × Real => (R i z.1).symm z.2))
    (hRzero : ∀ i s, R i 0 s = s)
    (K : ι → Set Real) (hK : ∀ i, IsCompact (K i))
    (hRfix : ∀ i t s, s ∉ K i → R i t s = s)
    (raw : ι → Real × Real → E) (L P : Real → Set E) (C : Set E)
    (hPC : ∀ t ∈ Icc (-eta) eta, P t ⊆ C)
    (hcuts : ∀ t ∈ Icc (-eta) eta,
      (⋃ i, (fun x => raw i (t, x)) '' Icc (A i t) (B i t)) = L t \ P t)
    (hlevel : ∀ i t, t ∈ Icc (-eta) eta → ∀ x ∈ Icc (l i) (u i),
      raw i (t, R i t x) ∈ L t) :
    ∃ δ : Real, 0 < δ ∧ δ ≤ eta ∧ ∀ t ∈ Icc (-δ) δ,
      (∀ i, l i < (R i t).symm (A i t) ∧
        (R i t).symm (A i t) < (R i t).symm (B i t) ∧
        (R i t).symm (B i t) < u i) ∧
      (∀ i, (fun x => raw i (t, R i t x)) ''
        Icc ((R i t).symm (A i t)) ((R i t).symm (B i t)) =
          (fun x => raw i (t, x)) '' Icc (A i t) (B i t)) ∧
      (L t \ P t ⊆ ⋃ i, (fun x => raw i (t, R i t x)) '' Icc (l i) (u i)) ∧
      L t \ C = (⋃ i, (fun x => raw i (t, R i t x)) '' Icc (l i) (u i)) \ C := by
  obtain ⟨δ, hδ, hδη, hbounds⟩ := exists_uniform_inverse_cut_bounds
    heta l u A B hA hB hlA hAB hBu R hRinv hRzero
  have htime {t : Real} (ht : t ∈ Icc (-δ) δ) : t ∈ Icc (-eta) eta :=
    ⟨by linarith [ht.1], ht.2.trans hδη⟩
  refine ⟨δ, hδ, hδη, ?_⟩
  intro t ht
  have himage (i : ι) : (fun x => raw i (t, R i t x)) ''
      Icc ((R i t).symm (A i t)) ((R i t).symm (B i t)) =
        (fun x => raw i (t, x)) '' Icc (A i t) (B i t) :=
    image_reparametrized_Icc_inverse_endpoints (fun x => raw i (t, x))
      (R i t) (hK i) (hRfix i t) (A i t) (B i t)
  have hcover : L t \ P t ⊆
      ⋃ i, (fun x => raw i (t, R i t x)) '' Icc (l i) (u i) := by
    rw [← hcuts t (htime ht)]
    apply iUnion_mono
    intro i
    rw [← himage i]
    exact image_mono (Icc_subset_Icc (hbounds t ht i).1.le (hbounds t ht i).2.2.le)
  refine ⟨hbounds t ht, himage, hcover, ?_⟩
  apply sdiff_eq_of_exterior_coverage _ _ (P t) _ ?_ hcover (hPC t (htime ht))
  apply iUnion_subset
  intro i z hz
  obtain ⟨x, hx, rfl⟩ := hz
  exact hlevel i t (htime ht) x hx

private theorem central_strip_interior_notMem_closedSquare {M : Type*} [TopologicalSpace M]
    {h : M → Real} {c r : Real}
    (e : OpenPartialHomeomorph E2 M) (hr : 0 < r)
    (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c - x 0 ^ 2 + x 1 ^ 2)
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) M)
    (a b a₀ b₀ : Fin 2 → Real)
    (hchain : ∀ i, a i < a₀ i ∧ a₀ i < b₀ i ∧ b₀ i < b i)
    (hsource : ∀ i, Icc (a i) (b i) ×ˢ ({0} : Set Real) ⊆ (F i).source)
    (hheight : ∀ i z, z ∈ (F i).source → h (F i z) = c + z.2)
    (hdisjoint : Pairwise (fun i j => Disjoint (F i).target (F j).target))
    (hcover : (⋃ i, F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
      (h ⁻¹' {c}) \ e '' openSquare r)
    (hends : ∀ i, range (fun j : Fin 2 × Fin 2 => e (contact r j)) ∩
      (F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
        {F i (a₀ i, 0), F i (b₀ i, 0)})
    (i : Fin 2) {s : Real} (hs : s ∈ Ioo (a₀ i) (b₀ i)) :
    F i (s, 0) ∉ e '' closedSquare r := by
  have hc := hchain i
  have hsi : s ∈ Icc (a i) (b i) :=
    ⟨hc.1.le.trans hs.1.le, hs.2.le.trans hc.2.2.le⟩
  have hs0 : (s, 0) ∈ (F i).source := hsource i ⟨hsi, rfl⟩
  have hsout := (central_strip_exterior_iff F a b a₀ b₀ hchain hsource hheight
    hdisjoint hcover i hsi).mpr (Ioo_subset_Icc_self hs)
  rintro ⟨x, hx, he⟩
  have hlev : h (F i (s, 0)) = c := by simpa using hheight i (s, 0) hs0
  have hzero : x 0 ^ 2 = x 1 ^ 2 := by
    rw [← he, hform x (hrs hx)] at hlev
    linarith
  have hxo : x ∉ openSquare r := fun hxo => hsout ⟨x, hxo, he⟩
  obtain ⟨j, rfl⟩ := (square_boundary_zeroLevel hr).subset ⟨⟨hx, hxo⟩, hzero⟩
  have hend : F i (s, 0) ∈ ({F i (a₀ i, 0), F i (b₀ i, 0)} : Set M) :=
    (hends i).subset ⟨⟨j, he⟩, (s, 0), ⟨Ioo_subset_Icc_self hs, rfl⟩, rfl⟩
  have ha0 : (a₀ i, 0) ∈ (F i).source :=
    hsource i ⟨⟨hc.1.le, hc.2.1.le.trans hc.2.2.le⟩, rfl⟩
  have hb0 : (b₀ i, 0) ∈ (F i).source :=
    hsource i ⟨⟨hc.1.le.trans hc.2.1.le, hc.2.2.le⟩, rfl⟩
  rcases mem_insert_iff.mp hend with heq | heq
  · have hh := congrArg Prod.fst ((F i).injOn hs0 ha0 heq)
    exact hs.1.ne' hh
  · have hh := congrArg Prod.fst ((F i).injOn hs0 hb0 (mem_singleton_iff.mp heq))
    exact hs.2.ne hh

private theorem compact_middle_arcs_disjoint_projected_square
    {M : Type*} [TopologicalSpace M] {h : M → Real} {c r : Real}
    (e : OpenPartialHomeomorph E2 M) (hr : 0 < r)
    (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c - x 0 ^ 2 + x 1 ^ 2)
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) M)
    (a b a₀ b₀ : Fin 2 → Real)
    (hchain : ∀ i, a i < a₀ i ∧ a₀ i < b₀ i ∧ b₀ i < b i)
    (hsource : ∀ i, Icc (a i) (b i) ×ˢ ({0} : Set Real) ⊆ (F i).source)
    (hheight : ∀ i z, z ∈ (F i).source → h (F i z) = c + z.2)
    (hdisjoint : Pairwise (fun i j => Disjoint (F i).target (F j).target))
    (hcover : (⋃ i, F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
      (h ⁻¹' {c}) \ e '' openSquare r)
    (hends : ∀ i, range (fun j : Fin 2 × Fin 2 => e (contact r j)) ∩
      (F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
        {F i (a₀ i, 0), F i (b₀ i, 0)})
    (G : M → E3) (hG : Continuous G) (hGinj : Function.Injective G)
    (hGzero : ∀ i s, s ∈ Icc (a₀ i) (b₀ i) → G (F i (s, 0)) 2 = 0)
    (l₁ u₁ : Fin 2 → Real)
    (hcuts : ∀ i, a₀ i < l₁ i ∧ l₁ i ≤ u₁ i ∧ u₁ i < b₀ i) :
    let Q : Set E3 := G '' (e '' closedSquare r)
    let B : Set E2 :=
      ⋃ i, (fun s => Saddle.toE2 (G (F i (s, 0)))) '' Icc (l₁ i) (u₁ i)
    IsCompact Q ∧ IsCompact B ∧
      Disjoint (Saddle.toE2 '' (Q ∩ {y : E3 | y 2 = 0})) B := by
  have hcentral (i : Fin 2) {s : Real} (hs : s ∈ Icc (l₁ i) (u₁ i)) :
      s ∈ Ioo (a₀ i) (b₀ i) :=
    ⟨(hcuts i).1.trans_le hs.1, hs.2.trans_lt (hcuts i).2.2⟩
  have hsource' (i : Fin 2) {s : Real} (hs : s ∈ Icc (l₁ i) (u₁ i)) :
      (s, 0) ∈ (F i).source :=
    hsource i ⟨⟨(hchain i).1.le.trans (hcentral i hs).1.le,
      (hcentral i hs).2.le.trans (hchain i).2.2.le⟩, rfl⟩
  have hcont (i : Fin 2) :
      ContinuousOn (fun s => Saddle.toE2 (G (F i (s, 0)))) (Icc (l₁ i) (u₁ i)) :=
    contDiff_toE2.continuous.comp_continuousOn (hG.comp_continuousOn
      ((F i).continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs => hsource' i hs)))
  refine ⟨((isCompact_closedSquare hr.le).image_of_continuousOn
    (e.continuousOn.mono hrs)).image hG,
    isCompact_iUnion (fun i => isCompact_Icc.image_of_continuousOn (hcont i)), ?_⟩
  apply disjoint_left.mpr
  intro v hvQ hvB
  obtain ⟨x, ⟨hxQ, hxzero⟩, hxv⟩ := hvQ
  obtain ⟨q, hq, hGq⟩ := hxQ
  obtain ⟨i, s, hs, hsv⟩ := mem_iUnion.mp hvB
  change Saddle.toE2 (G (F i (s, 0))) = v at hsv
  have hproj : Saddle.toE2 (G (F i (s, 0))) = Saddle.toE2 x := hsv.trans hxv.symm
  have hGzero' := hGzero i s (Ioo_subset_Icc_self (hcentral i hs))
  have hGx : G (F i (s, 0)) = x := by
    ext k
    fin_cases k
    · have hh := congrArg (fun y : E2 => y 0) hproj
      simpa [Saddle.toE2] using hh
    · have hh := congrArg (fun y : E2 => y 1) hproj
      simpa [Saddle.toE2] using hh
    · exact hGzero'.trans hxzero.symm
  have hFq : F i (s, 0) = q := hGinj (hGx.trans hGq.symm)
  apply central_strip_interior_notMem_closedSquare e hr hrs hform F a b a₀ b₀
    hchain hsource hheight hdisjoint hcover hends i (hcentral i hs)
  exact hFq ▸ hq

private theorem eq_of_planarProjection_and_height {x y : E3}
    (hxy : Saddle.toE2 x = Saddle.toE2 y) (hheight : x 2 = y 2) : x = y := by
  ext k
  fin_cases k
  · have hh := congrArg (fun z : E2 => z 0) hxy
    simpa [Saddle.toE2] using hh
  · have hh := congrArg (fun z : E2 => z 1) hxy
    simpa [Saddle.toE2] using hh
  · exact hheight

private theorem pairwise_disjoint_reparametrized_central_planar_traces
    {M : Type*} [TopologicalSpace M]
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) M)
    (l u : Fin 2 → Real)
    (hsource : ∀ i, Icc (l i) (u i) ×ˢ ({0} : Set Real) ⊆ (F i).source)
    (hdisjoint : Pairwise (fun i j => Disjoint (F i).target (F j).target))
    (G : M → E3) (hGinj : Function.Injective G)
    (hGzero : ∀ i s, s ∈ Icc (l i) (u i) → G (F i (s, 0)) 2 = 0)
    (R : Fin 2 → Real → Real → Real) (hRzero : ∀ i s, R i 0 s = s) :
    let mu : Fin 2 → Real × Real → E2 :=
      fun i z => Saddle.toE2 (G (F i (R i z.1 z.2, z.1)))
    Pairwise (fun i j =>
      Disjoint (mu i '' (({0} : Set Real) ×ˢ Icc (l i) (u i)))
        (mu j '' (({0} : Set Real) ×ˢ Icc (l j) (u j)))) := by
  dsimp only
  intro i j hij
  apply disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨⟨t, s⟩, ⟨ht, hs⟩, heqi⟩ := hxi
  obtain ⟨⟨v, q⟩, ⟨hv, hq⟩, heqj⟩ := hxj
  have ht0 : t = 0 := ht
  have hv0 : v = 0 := hv
  subst t
  subst v
  simp only [hRzero] at heqi heqj
  have hG : G (F i (s, 0)) = G (F j (q, 0)) :=
    eq_of_planarProjection_and_height (heqi.trans heqj.symm)
      ((hGzero i s hs).trans (hGzero j q hq).symm)
  have hF : F i (s, 0) = F j (q, 0) := hGinj hG
  have hsi : (s, 0) ∈ (F i).source := hsource i ⟨hs, rfl⟩
  have hqj : (q, 0) ∈ (F j).source := hsource j ⟨hq, rfl⟩
  exact disjoint_left.mp (hdisjoint hij)
    ((F i).map_source hsi) (hF ▸ (F j).map_source hqj)

private theorem projected_fiber_sdiff_eq_of_patch_union_slice
    {X Q Qclosed : Set E3} {S C : Set E2} {delta t : Real}
    (hfiber : X = Q ∪ Saddle.slice S t) (hQ : Q ⊆ Qclosed)
    (hQheight : ∀ y ∈ Q, y 2 = t)
    (hC : ∀ y ∈ Qclosed, y 2 ∈ Icc (-delta) delta → Saddle.toE2 y ∈ C)
    (ht : t ∈ Icc (-delta) delta) :
    (Saddle.toE2 '' X) \ C = S \ C := by
  have hQC : Saddle.toE2 '' Q ⊆ C := by
    rintro x ⟨y, hy, rfl⟩
    exact hC y (hQ hy) ((hQheight y hy).symm ▸ ht)
  have hslice : Saddle.toE2 '' Saddle.slice S t = S := by
    apply Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hy.1
    · intro x hx
      have hcoord : Saddle.toE2 (Saddle.toE3 x t) = x := by
        ext i
        fin_cases i <;> rfl
      exact ⟨Saddle.toE3 x t, ⟨hcoord.symm ▸ hx, rfl⟩, hcoord⟩
  rw [hfiber, image_union, hslice, union_sdiff_distrib,
    sdiff_eq_empty.mpr hQC, empty_union]

private theorem planar_level_inter_eq_of_common_spatial_patch
    {A B U : Set E3} {C : Set E2} {t : Real}
    (hcommon : A ∩ U = B ∩ U)
    (hlift : ∀ x ∈ C, Saddle.toE3 x t ∈ U) :
    {x : E2 | Saddle.toE3 x t ∈ A} ∩ C =
      {x : E2 | Saddle.toE3 x t ∈ B} ∩ C := by
  ext x
  constructor
  · rintro ⟨hxA, hxC⟩
    have hx : Saddle.toE3 x t ∈ A ∩ U := ⟨hxA, hlift x hxC⟩
    rw [hcommon] at hx
    exact ⟨hx.1, hxC⟩
  · rintro ⟨hxB, hxC⟩
    have hx : Saddle.toE3 x t ∈ B ∩ U := ⟨hxB, hlift x hxC⟩
    rw [← hcommon] at hx
    exact ⟨hx.1, hxC⟩

private theorem planar_level_eq_projected_height_slice (A : Set E3) (t : Real) :
    {x : E2 | Saddle.toE3 x t ∈ A} =
      Saddle.toE2 '' (A ∩ {y : E3 | y 2 = t}) := by
  ext x
  constructor
  · intro hx
    refine ⟨Saddle.toE3 x t, ⟨hx, rfl⟩, ?_⟩
    ext i
    fin_cases i <;> rfl
  · rintro ⟨y, ⟨hyA, hyheight⟩, hyx⟩
    have heq : Saddle.toE3 x t = y := by
      apply eq_of_planarProjection_and_height
      · rw [← hyx]
        ext i
        fin_cases i <;> rfl
      · exact hyheight.symm
    change Saddle.toE3 x t ∈ A
    rw [heq]
    exact hyA

private theorem exists_stationary_model_arc_of_endpoint_contacts
    (G₀ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ x : E3, D x 2 = x 2)
    (hDzero : ∀ x : E3, x 2 = 0 → D x = x)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (hF : ContMDiffOn 𝓘(Real, Real × Real) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) 𝓘(Real, Real × Real) ∞ F.symm F.target)
    {scale : Real} (hscale : 0 < scale)
    (hheight : ∀ z ∈ F.source, G₀ (F z) 2 = scale * z.2)
    {v a₀ b₀ w : Real} (hva₀ : v < a₀) (ha₀b₀ : a₀ < b₀) (hb₀w : b₀ < w)
    (hFcentral : ∀ x ∈ Ioo v w, (x, 0) ∈ F.source)
    (g : S2 → E3) (hg : Continuous g) (hginj : Injective g)
    {U : Set E3} (hU : IsOpen U)
    (hcommon : (G₀ '' sphere (0 : E3) 1) ∩ U = range g ∩ U)
    (Fa : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
    (a b : Fin 2 → Real) {eta : Real} (heta : 0 < eta)
    (hFa : ∀ i, Ioo (a i) (b i) ×ˢ Ioo (-eta) eta ⊆ (Fa i).source)
    (hactualheight : ∀ i z, z ∈ Ioo (a i) (b i) ×ˢ Ioo (-eta) eta →
      g (Fa i z) 2 = z.2)
    (hflat : ∀ i x, x ∈ Icc (a i) (b i) → ∀ t ∈ Ioo (-eta) eta,
      D (g (Fa i (x, t))) =
        g (Fa i (x, 0)) + t • (EuclideanSpace.single 2 1 : E3))
    (j₀ j₁ : Fin 2) (q₀ q₁ : Real)
    (hq₀ : q₀ ∈ Ioo (a j₀) (b j₀)) (hq₁ : q₁ ∈ Ioo (a j₁) (b j₁))
    (hcontact₀ : G₀ (F (a₀, 0)) = g (Fa j₀ (q₀, 0)))
    (hcontact₁ : G₀ (F (b₀, 0)) = g (Fa j₁ (q₁, 0)))
    (hcontactU₀ : G₀ (F (a₀, 0)) ∈ U) (hcontactU₁ : G₀ (F (b₀, 0)) ∈ U) :
    ∃ (l l₀ l₁ u₁ u₀ u δ : Real) (K : Set Real),
      (v < l ∧ l < l₀ ∧ l₀ < a₀ ∧ a₀ < l₁ ∧ l₁ < u₁ ∧
        u₁ < b₀ ∧ b₀ < u₀ ∧ u₀ < u ∧ u < w) ∧
      0 < δ ∧ δ ≤ eta ∧ IsCompact K ∧ K ⊆ Ioo v w ∧
      ∃ R : Real → Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞,
        (∀ x, R 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × Real => R z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × Real => (R z.1).symm z.2) ∧
        (∀ t x, x ∉ K → R t x = x) ∧
        let μ : Real × Real → E2 :=
          fun z => toE2 (D (G₀ (F (R z.1 z.2, z.1 / scale))))
        ∃ V : Set (Real × Real), IsOpen V ∧ Icc (-δ) δ ×ˢ Icc l u ⊆ V ∧
          ContDiffOn Real ∞ μ V ∧
          (∀ t ∈ Icc (-δ) δ, InjOn (fun x => μ (t, x)) (Icc l u)) ∧
          (∀ t ∈ Icc (-δ) δ, ∀ x ∈ Icc l u,
            deriv (fun z => μ (t, z)) x ≠ 0) ∧
          (∀ x ∈ Ioo v w, μ (0, x) = toE2 (G₀ (F (x, 0)))) ∧
          (∀ t ∈ Icc (-δ) δ, ∀ x ∈ Icc l u,
            (R t x, t / scale) ∈ F.source) ∧
          (∀ t ∈ Icc (-δ) δ, ∀ x ∈ Icc l l₁ ∪ Icc u₁ u,
            μ (t, x) = μ (0, x)) ∧
          ∀ t ∈ Icc (-δ) δ, ∀ x ∈ Icc l l₁ ∪ Icc u₁ u,
            D (G₀ (F (R t x, t / scale))) =
              G₀ (F (x, 0)) + t • (EuclideanSpace.single 2 1 : E3) := by
  let gamma : Real → E3 := fun x => G₀ (F (x, 0))
  have hgamma : ContDiffOn Real ∞ gamma (Ioo v w) := by
    have hG : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun p : S2 => G₀ p) :=
      G₀.contMDiff.comp (contMDiff_coe_sphere (n := 2) (m := ∞) (E := E3))
    exact (hG.comp_contMDiffOn
      (hF.comp (contDiff_id.prodMk contDiff_const).contMDiff.contMDiffOn
        (fun x hx => hFcentral x hx))).contDiffOn
  have hgammaZ : MapsTo gamma (Ioo v w) (G₀ '' sphere (0 : E3) 1) := by
    intro x _
    exact ⟨F (x, 0), (F (x, 0)).property, rfl⟩
  have hgammaheight (x : Real) (hx : x ∈ Ioo v w) : gamma x 2 = 0 := by
    dsimp only [gamma]
    rw [hheight _ (hFcentral x hx), mul_zero]
  obtain ⟨N, l, l₀, l₁, u₁, u₀, u, χ, d₀, W, _, _, _, _, _, _,
      hchain, _, hχ, hχcompact, hχsupport, _, hχone, hd₀, _, hW, hWrect, _,
      hy, hyactual, hyheight, hyvertical⟩ :=
    exists_endpoint_cutoff_and_vertical_germ g hg hginj hU hcommon.symm Fa a b heta
      hFa hactualheight gamma hva₀ ha₀b₀ hb₀w hgamma hgammaZ hgammaheight
      j₀ j₁ q₀ q₁ hq₀ hq₁ hcontact₀ hcontact₁ hcontactU₀ hcontactU₁ D hDzero hflat
  let G := G₀.trans D
  let Fp := physicalHeightStrip hscale.ne' F
  have hFpheight : ∀ z ∈ Fp.source, G (Fp z) 2 = z.2 := by
    apply physicalHeightStrip_height hscale.ne' F G
    intro z hz
    change D (G₀ (F z)) 2 = scale * z.2
    rw [hDheight, hheight z hz]
  have hcommon' : (G '' sphere (0 : E3) 1) ∩ (D '' U) =
      range (D ∘ g) ∩ (D '' U) := by
    have hGimage : G '' sphere (0 : E3) 1 = D '' (G₀ '' sphere (0 : E3) 1) := by
      rw [image_image]
      rfl
    have hDi : Injective (fun x : E3 => D x) := D.injective
    rw [hGimage, ← image_inter hDi, hcommon, image_inter hDi, range_comp]
  have hvl : v < l := hchain.1
  have huw : u < w := hchain.2.2.2.2.2.2.2.2
  let ε : Real := min (l - v) (w - u) / 2
  have hmin : 0 < min (l - v) (w - u) := lt_min (by linarith) (by linarith)
  have hε : 0 < ε := half_pos hmin
  have hεl : ε < l - v := (half_lt_self hmin).trans_le (min_le_left _ _)
  have hεu : ε < w - u := (half_lt_self hmin).trans_le (min_le_right _ _)
  have hpad : Icc (l - ε) (u + ε) ⊆ Ioo v w := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hFpcentral (x : Real) (hx : x ∈ Icc (l - ε) (u + ε)) : (x, 0) ∈ Fp.source := by
    rw [physicalHeightStrip_source]
    simpa only [mem_ofPred_eq, zero_div] using hFcentral x (hpad hx)
  let y : Real × Real → E3 :=
    fun z => gamma z.2 + z.1 • (EuclideanSpace.single 2 1 : E3)
  have hWzero (x : Real) (hx : x ∈ tsupport χ) : (0, x) ∈ W :=
    hWrect ⟨⟨by linarith, hd₀.le⟩, hx⟩
  have hFpsource (x : Real) (hx : x ∈ tsupport χ) : (x, 0) ∈ Fp.source := by
    rw [physicalHeightStrip_source]
    simpa only [mem_ofPred_eq, zero_div] using hFcentral x (hχsupport hx).2
  have hycentral (x : Real) (hx : x ∈ tsupport χ) : y (0, x) = G (Fp (x, 0)) := by
    change gamma x + (0 : Real) • _ = D (G₀ (physicalHeightStrip hscale.ne' F (x, 0)))
    rw [zero_smul, add_zero, physicalHeightStrip_central]
    exact (hDzero _ (hgammaheight x (hχsupport hx).2)).symm
  obtain ⟨d, hd, R, hRzero, hR, hRinv, hRfix, V, hV, hVrect, hμ,
      hμinj, hμder, hμzero, hμsource, hμstationary, hμends⟩ :=
    exists_stationary_regular_planar_strip G (F (a₀, 0)) Fp
      (physicalHeightStrip_smooth hscale.ne' F hF)
      (physicalHeightStrip_symm_smooth hscale.ne' F hFi) hFpheight
      l l₁ u₁ u hε hFpcentral (D ∘ g) (D '' U) hcommon' y hW hy
      (fun z hz => (hyactual hz).1) (fun z hz => (hyactual hz).2) hyheight hyvertical
      χ hχ hχcompact hχone hWzero hFpsource hycentral
  let δ := min d eta
  have hδ : 0 < δ := lt_min hd heta
  have htime {t : Real} (ht : t ∈ Icc (-δ) δ) : t ∈ Icc (-d) d :=
    ⟨by linarith [ht.1, min_le_left d eta], ht.2.trans (min_le_left _ _)⟩
  have hμeq : (fun z : Real × Real => toE2 (G (Fp (R z.1 z.2, z.1)))) =
      (fun z : Real × Real => toE2 (D (G₀ (F (R z.1 z.2, z.1 / scale))))) := by
    funext z
    change toE2 (D (G₀ (physicalHeightStrip hscale.ne' F (R z.1 z.2, z.1)))) = _
    rw [physicalHeightStrip_apply]
  rw [hμeq] at hμ hμinj hμder hμstationary
  refine ⟨l, l₀, l₁, u₁, u₀, u, δ, tsupport χ, hchain, hδ, min_le_right _ _,
    hχcompact.isCompact, fun x hx => (hχsupport hx).2,
    R, hRzero, hR, hRinv, hRfix, V, hV, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact hVrect ⟨htime hz.1, hz.2⟩
  · exact hμ
  · intro t ht
    exact hμinj t (htime ht)
  · intro t ht x hx
    exact hμder t (htime ht) x hx
  · intro x hx
    simp only [hRzero, zero_div]
    exact congrArg toE2 (hDzero _ (hgammaheight x hx))
  · intro t ht x hx
    have hmem := hμsource t (htime ht) x hx
    rw [physicalHeightStrip_source] at hmem
    exact hmem
  · intro t ht x hx
    exact hμstationary t (htime ht) x hx
  · intro t ht x hx
    have hmatch := hμends t (htime ht) x hx
    change D (G₀ (physicalHeightStrip hscale.ne' F (R t x, t))) = _ at hmatch
    simpa only [physicalHeightStrip_apply] using hmatch

private theorem restricted_nested_morse_chart
    (d : OpenPartialHomeomorph E2 S2) (p : S2)
    (hdp : d 0 = p)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    {ρ r : Real} (hρ : 0 < ρ) (hr : 0 ≤ r) (hrρ : 2 * r < ρ)
    (hsource : closedBall (0 : E2) ρ ⊆ d.source)
    (hform : ∀ x ∈ closedBall (0 : E2) ρ,
      height (d x) = height p - x 0 ^ 2 + x 1 ^ 2) :
    let e := d.restrOpen (ball (0 : E2) ρ) isOpen_ball
    0 ∈ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      closedSquare r ⊆ e.source ∧
      (∀ x ∈ e.source, height (e x) = height p - x 0 ^ 2 + x 1 ^ 2) ∧
      (∀ x, e x = d x) := by
  let e := d.restrOpen (ball (0 : E2) ρ) isOpen_ball
  have hes : e.source = ball (0 : E2) ρ := by
    rw [d.restrOpen_source]
    exact inter_eq_right.mpr (ball_subset_closedBall.trans hsource)
  refine ⟨?_, hdp, hd.mono inter_subset_left, hdi.mono inter_subset_left, ?_, ?_,
    fun _ => rfl⟩
  · change 0 ∈ e.source
    rw [hes, mem_ball, dist_self]
    exact hρ
  · intro x hx
    change x ∈ e.source
    rw [hes, mem_ball_zero_iff]
    exact (mem_closedBall_zero_iff.mp (closedSquare_subset_closedBall hr hx)).trans_lt hrρ
  · intro x hx
    exact hform x (ball_subset_closedBall (hes ▸ hx))

private theorem exists_common_neighborhood_for_model_square
    {g : S2 → E3} (hg : Continuous g) (hgi : Injective g)
    (e d : OpenPartialHomeomorph E2 S2)
    (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    {s ρ r : Real} (hs : 0 < s) (hr : 0 ≤ r) (hrρ : 2 * r < ρ)
    (hd : closedBall (0 : E2) ρ ⊆ d.source)
    (he : ∀ x ∈ closedBall (0 : E2) ρ, Real.sqrt s • x ∈ e.source)
    (hmatch : ∀ x ∈ closedBall (0 : E2) ρ,
      G (d x) = g (e (Real.sqrt s • x))) :
    ∃ U : Set E3, IsOpen U ∧ (fun q : S2 => G q) '' (d '' closedSquare r) ⊆ U ∧
      (G '' sphere (0 : E3) 1) ∩ U = range g ∩ U := by
  have hroot : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  obtain ⟨U, hU, hpatch, hcommon⟩ := exists_common_neighborhood_of_matching
    hg hgi G (Diffeomorph.refl (𝓡 3) E3 ∞) hs (mul_nonneg hroot.le hr)
    (show 2 * (Real.sqrt s * r) < Real.sqrt s * ρ by nlinarith)
    hd he hmatch
  refine ⟨U, hU, ?_, ?_⟩
  · rintro y ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hxball : x ∈ closedBall (0 : E2) ρ :=
      (closedBall_subset_closedBall hrρ.le) (closedSquare_subset_closedBall hr hx)
    have hxscaled : Real.sqrt s • x ∈ closedSquare (Real.sqrt s * r) := by
      constructor
      · simpa only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hroot] using
          mul_le_mul_of_nonneg_left hx.1 hroot.le
      · simpa only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hroot] using
          mul_le_mul_of_nonneg_left hx.2 hroot.le
    change G (d x) ∈ U
    rw [hmatch x hxball]
    exact hpatch ⟨Real.sqrt s • x, hxscaled, rfl⟩
  · change (id '' range g) ∩ U = (G '' sphere (0 : E3) 1) ∩ U at hcommon
    simpa only [image_id] using hcommon.symm

local notation "IR2" => 𝓘(Real, Real × Real)

private theorem smul_contact (a r : Real) (j : Fin 2 × Fin 2) :
    a • contact r j = contact (a * r) j := by
  ext i
  fin_cases i <;> simp [contact, mul_ite]

private theorem smul_image_closedSquare {a : Real} (ha : 0 < a) (r : Real) :
    (fun x : E2 => a • x) '' closedSquare r = closedSquare (a * r) := by
  have hmem (x : E2) : a • x ∈ closedSquare (a * r) ↔ x ∈ closedSquare r := by
    change (|a * x 0| ≤ a * r ∧ |a * x 1| ≤ a * r) ↔ _
    simp only [abs_mul, abs_of_pos ha, mul_le_mul_iff_of_pos_left ha]
    rfl
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).mpr hx
  · intro hy
    have hback : a • (a⁻¹ • y) = y := by
      rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    refine ⟨a⁻¹ • y, (hmem _).mp ?_, hback⟩
    rwa [hback]

private theorem smul_image_openSquare {a : Real} (ha : 0 < a) (r : Real) :
    (fun x : E2 => a • x) '' openSquare r = openSquare (a * r) := by
  have hmem (x : E2) : a • x ∈ openSquare (a * r) ↔ x ∈ openSquare r := by
    change (|a * x 0| < a * r ∧ |a * x 1| < a * r) ↔ _
    simp only [abs_mul, abs_of_pos ha, mul_lt_mul_iff_of_pos_left ha]
    rfl
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).mpr hx
  · intro hy
    have hback : a • (a⁻¹ • y) = y := by
      rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    refine ⟨a⁻¹ • y, (hmem _).mp ?_, hback⟩
    rwa [hback]

private theorem matching_square_images_of_positive_scale
    (e d : E2 → S2) (G₀ : E3 → E3) (g : S2 → E3)
    {s r : Real} (hs : 0 < s)
    (hmatch : ∀ x ∈ closedSquare r, G₀ (d x) = g (e (Real.sqrt s • x))) :
    G₀ '' ((fun x => (d x : E3)) '' closedSquare r) =
        g '' (e '' closedSquare (Real.sqrt s * r)) ∧
      G₀ '' ((fun x => (d x : E3)) '' openSquare r) =
        g '' (e '' openSquare (Real.sqrt s * r)) := by
  have hclosed : (fun x => G₀ (d x)) '' closedSquare r =
      (fun x => g (e (Real.sqrt s • x))) '' closedSquare r := by
    apply image_congr
    exact hmatch
  have hopen : (fun x => G₀ (d x)) '' openSquare r =
      (fun x => g (e (Real.sqrt s • x))) '' openSquare r := by
    apply image_congr
    exact fun x hx => hmatch x (openSquare_subset_closedSquare r hx)
  constructor
  · rw [image_image, hclosed, ← smul_image_closedSquare (Real.sqrt_pos.mpr hs)]
    rw [image_image, image_image]
  · rw [image_image, hopen, ← smul_image_openSquare (Real.sqrt_pos.mpr hs)]
    rw [image_image, image_image]

private theorem matching_contact_transfer
    (e d : E2 → S2) (G₀ : E3 → E3) (g : S2 → E3)
    {scale r : Real} (hr : 0 < r)
    (hmatch : ∀ x ∈ closedSquare r, G₀ (d x) = g (e (scale • x)))
    (Fa Fm : Fin 2 → Real × Real → S2)
    (a b aa₀ ab₀ ma₀ mb₀ : Fin 2 → Real)
    (hchain : ∀ i, a i < aa₀ i ∧ aa₀ i < ab₀ i ∧ ab₀ i < b i)
    (La Lm : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2))
    (hLa : ∀ k, Fa k.1 (stripEndpoint aa₀ ab₀ k, 0) =
      e (contact (scale * r) (La k)))
    (hLm : ∀ k, Fm k.1 (stripEndpoint ma₀ mb₀ k, 0) = d (contact r (Lm k)))
    {U : Set E3}
    (hQU : G₀ '' ((fun x => (d x : E3)) '' closedSquare r) ⊆ U)
    (j : Fin 2 × Fin 2) :
    let k := La.symm (Lm j)
    let q := if k.2 = 0 then aa₀ k.1 else ab₀ k.1
    q ∈ Ioo (a k.1) (b k.1) ∧
      G₀ (Fm j.1 (stripEndpoint ma₀ mb₀ j, 0)) = g (Fa k.1 (q, 0)) ∧
      G₀ (Fm j.1 (stripEndpoint ma₀ mb₀ j, 0)) ∈ U := by
  let k := La.symm (Lm j)
  change stripEndpoint aa₀ ab₀ k ∈ Ioo (a k.1) (b k.1) ∧ _
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [stripEndpoint]
    split_ifs
    · exact ⟨(hchain k.1).1, (hchain k.1).2.1.trans (hchain k.1).2.2⟩
    · exact ⟨(hchain k.1).1.trans (hchain k.1).2.1, (hchain k.1).2.2⟩
  · change G₀ (Fm j.1 (stripEndpoint ma₀ mb₀ j, 0)) =
      g (Fa k.1 (stripEndpoint aa₀ ab₀ k, 0))
    rw [hLm j, hLa k, hmatch _ (contact_mem hr (Lm j)).1.1, smul_contact]
    simp [k]
  · rw [hLm j]
    exact hQU ⟨(d (contact r (Lm j)) : E3),
      ⟨contact r (Lm j), (contact_mem hr (Lm j)).1.1, rfl⟩, rfl⟩

theorem exists_raw_recut_model_strips
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {p : S2} (hunique : ∀ q, h q = h p →
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q = p)
    (hconnected : IsPreconnected (h ⁻¹' {h p}))
    (d : OpenPartialHomeomorph E2 S2) (hd0 : 0 ∈ d.source) (hdp : d 0 = p)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    (hform : ∀ x ∈ d.source, h (d x) = h p - x 0 ^ 2 + x 1 ^ 2)
    {r epsilon : Real} (hr : 0 < r) (hrs : closedSquare r ⊆ d.source)
    (hepsilon : 0 < epsilon) :
    ∃ (a b a₀ b₀ : Fin 2 → Real) (eta delta : Real)
        (F : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
        (L : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2)) (A B : Fin 2 → Real → Real),
      0 < delta ∧ delta < eta ∧ eta < epsilon ∧ delta < r ^ 2 ∧
      (∀ i, a i < a₀ i ∧ a₀ i < b₀ i ∧ b₀ i < b i) ∧
      (∀ i, Icc (a i) (b i) ×ˢ Icc (-eta) eta ⊆ (F i).source) ∧
      (∀ i, ContMDiffOn IR2 (𝓡 2) ∞ (F i) (F i).source) ∧
      (∀ i, ContMDiffOn (𝓡 2) IR2 ∞ (F i).symm (F i).target) ∧
      (∀ i z, z ∈ (F i).source → h (F i z) = h p + z.2) ∧
      Pairwise (fun i j => Disjoint (F i).target (F j).target) ∧
      ((⋃ i, F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
        (h ⁻¹' {h p}) \ d '' openSquare r) ∧
      (∀ i, range (fun j : Fin 2 × Fin 2 => d (contact r j)) ∩
          (F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
        {F i (a₀ i, 0), F i (b₀ i, 0)}) ∧
      (∀ k, F k.1 (stripEndpoint a₀ b₀ k, 0) = d (contact r (L k))) ∧
      (∀ i, A i 0 = a₀ i ∧ B i 0 = b₀ i) ∧
      ∀ t ∈ Icc (-delta) delta,
        (∀ i, ContinuousAt (A i) t ∧ ContinuousAt (B i) t ∧
          a i < A i t ∧ A i t < B i t ∧ B i t < b i ∧
          (Icc (A i t) (B i t) ×ˢ ({t} : Set Real) ⊆ (F i).source) ∧
          F i (A i t, t) = d (movingContact r t (L (i, 0))) ∧
          F i (B i t, t) = d (movingContact r t (L (i, 1))) ∧
          (∀ s ∈ Icc (a i) (b i),
            F i (s, t) ∉ d '' openSquare r ↔ s ∈ Icc (A i t) (B i t))) ∧
        ((h ⁻¹' {h p + t}) \ d '' openSquare r) =
          ⋃ i, F i '' (Icc (A i t) (B i t) ×ˢ ({t} : Set Real)) := by
  obtain ⟨a, b, a₀, b₀, eta, F, heta, heta_epsilon, hchain, hrect,
      hF, hFi, hheight, hcentral, hdisjoint, hends, hband⟩ :=
    exists_whole_band_exterior_strips hh hunique hconnected
      d hd0 hdp hd hdi hform hr hrs hepsilon
  obtain ⟨delta, L, A, B, hdelta, hdelta_eta, hdelta_r, hL, hzero, hcuts⟩ :=
    exists_recut_exterior_strips d hr hrs hform F a b a₀ b₀ heta hchain hrect
      hheight hdisjoint hcentral hends hband
  exact ⟨a, b, a₀, b₀, eta, delta, F, L, A, B, hdelta, hdelta_eta, heta_epsilon,
    hdelta_r, hchain, hrect, hF, hFi, hheight, hdisjoint, hcentral, hends, hL,
    hzero, hcuts⟩

private theorem exists_raw_nested_recut_strips
    {p : S2} (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0)
    (hpz : (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8))
    (d : OpenPartialHomeomorph E2 S2) (hd0 : 0 ∈ d.source) (hdp : d 0 = p)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    (hform : ∀ x ∈ d.source, height (d x) = height p - x 0 ^ 2 + x 1 ^ 2)
    {r epsilon : Real} (hr : 0 < r) (hrs : closedSquare r ⊆ d.source)
    (hepsilon : 0 < epsilon) :
    ∃ (a b a₀ b₀ : Fin 2 → Real) (eta delta : Real)
        (F : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
        (L : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2)) (A B : Fin 2 → Real → Real),
      0 < delta ∧ delta < eta ∧ eta < epsilon ∧ delta < r ^ 2 ∧
      (∀ i, a i < a₀ i ∧ a₀ i < b₀ i ∧ b₀ i < b i) ∧
      (∀ i, Icc (a i) (b i) ×ˢ Icc (-eta) eta ⊆ (F i).source) ∧
      (∀ i, ContMDiffOn IR2 (𝓡 2) ∞ (F i) (F i).source) ∧
      (∀ i, ContMDiffOn (𝓡 2) IR2 ∞ (F i).symm (F i).target) ∧
      (∀ i z, z ∈ (F i).source → height (F i z) = height p + z.2) ∧
      Pairwise (fun i j => Disjoint (F i).target (F j).target) ∧
      ((⋃ i, F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
        (height ⁻¹' {height p}) \ d '' openSquare r) ∧
      (∀ i, range (fun j : Fin 2 × Fin 2 => d (contact r j)) ∩
          (F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
        {F i (a₀ i, 0), F i (b₀ i, 0)}) ∧
      (∀ k, F k.1 (stripEndpoint a₀ b₀ k, 0) = d (contact r (L k))) ∧
      (∀ i, A i 0 = a₀ i ∧ B i 0 = b₀ i) ∧
      ∀ t ∈ Icc (-delta) delta,
        (∀ i, ContinuousAt (A i) t ∧ ContinuousAt (B i) t ∧
          a i < A i t ∧ A i t < B i t ∧ B i t < b i ∧
          (Icc (A i t) (B i t) ×ˢ ({t} : Set Real) ⊆ (F i).source) ∧
          F i (A i t, t) = d (movingContact r t (L (i, 0))) ∧
          F i (B i t, t) = d (movingContact r t (L (i, 1))) ∧
          (∀ s ∈ Icc (a i) (b i),
            F i (s, t) ∉ d '' openSquare r ↔ s ∈ Icc (A i t) (B i t))) ∧
        ((height ⁻¹' {height p + t}) \ d '' openSquare r) =
          ⋃ i, F i '' (Icc (A i t) (B i t) ×ˢ ({t} : Set Real)) := by
  obtain ⟨p₀, hp₀z, hp₀height, hp₀crit, _⟩ := exists_unique_critical_point_in_height_band
  have hpp₀ : p = p₀ := critical_latitude_unique_in_saddle_interval hp hp₀crit
    (Ioo_subset_Icc_self hpz) (Ioo_subset_Icc_self hp₀z)
  have hpheight : height p ∈ Ioo (1 : Real) (41 / 40) := hpp₀ ▸ hp₀height
  have hunique (q : S2) (hq : height q = height p)
      (hqcrit : mfderiv (𝓡 2) 𝓘(Real, Real) height q = 0) : q = p := by
    apply (critical_in_height_band_iff_eq_saddle hp hpz q ?_).mp hqcrit
    rw [hq]
    exact ⟨hpheight.1.le, by linarith [hpheight.2]⟩
  exact exists_raw_recut_model_strips height_contMDiff hunique
    (isConnected_critical_level_of_saddle_latitude hp hpz).isPreconnected
    d hd0 hdp hd hdi hform hr hrs hepsilon

theorem projected_model_recut_strips
    (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (h : S2 → Real) (p : S2) (d : OpenPartialHomeomorph E2 S2)
    {scale u r : Real} (hscale : 0 < scale)
    (hheight : ∀ q : S2, G q 2 = scale * (h q - h p))
    (F : Fin 2 → Real × Real → S2) (A B : Fin 2 → Real)
    (hrecut : (h ⁻¹' {h p + u}) \ d '' openSquare r =
      ⋃ i, F i '' (Icc (A i) (B i) ×ˢ ({u} : Set Real))) :
    (⋃ i, (fun s => toE2 (G (F i (s, u)))) '' Icc (A i) (B i)) =
      {x : E2 | toE3 x (scale * u) ∈ G '' sphere (0 : E3) 1} \
        {x : E2 | toE3 x (scale * u) ∈
          (fun q : S2 => G q) '' (d '' openSquare r)} := by
  have hcoords (y : E3) (t : Real) (hy : y 2 = t) :
      toE3 (toE2 y) t = y := by
    ext j
    fin_cases j <;> simp_all [toE2, toE3]
  have hproject (x : E2) (t : Real) : toE2 (toE3 x t) = x := by
    ext j
    fin_cases j <;> rfl
  ext x
  constructor
  · intro hx
    obtain ⟨i, s, hs, rfl⟩ := mem_iUnion.mp hx
    have hq : F i (s, u) ∈ (h ⁻¹' {h p + u}) \ d '' openSquare r :=
      hrecut.symm.subset (mem_iUnion_of_mem i ⟨(s, u), ⟨hs, rfl⟩, rfl⟩)
    have hqheight : G (F i (s, u)) 2 = scale * u := by
      rw [hheight, show h (F i (s, u)) = h p + u from hq.1]
      ring
    change toE3 (toE2 (G (F i (s, u)))) (scale * u) ∈ G '' sphere (0 : E3) 1 ∧
      toE3 (toE2 (G (F i (s, u)))) (scale * u) ∉
        (fun q : S2 => G q) '' (d '' openSquare r)
    rw [hcoords _ _ hqheight]
    refine ⟨⟨_, (F i (s, u)).property, rfl⟩, ?_⟩
    rintro ⟨q, hqd, hqeq⟩
    have heq : q = F i (s, u) := Subtype.ext (G.injective hqeq)
    exact hq.2 (heq ▸ hqd)
  · rintro ⟨⟨q, hqs, hqx⟩, hxnot⟩
    let q' : S2 := ⟨q, hqs⟩
    have hqheight : h q' = h p + u := by
      have heq := congrArg (fun y : E3 => y 2) hqx
      change G q' 2 = scale * u at heq
      rw [hheight] at heq
      nlinarith
    have hqnot : q' ∉ d '' openSquare r := by
      intro hqd
      exact hxnot ⟨q', hqd, hqx⟩
    have hmem := hrecut.subset ⟨hqheight, hqnot⟩
    obtain ⟨i, z, hz, heq⟩ := mem_iUnion.mp hmem
    have hzu : z.2 = u := hz.2
    have heq' : F i (z.1, u) = q' := by simpa only [← hzu] using heq
    refine mem_iUnion_of_mem i ⟨z.1, hz.1, ?_⟩
    change toE2 (G (F i (z.1, u))) = x
    rw [heq']
    exact (congrArg toE2 hqx).trans (hproject x (scale * u))

theorem physical_projected_recut_model_strips
    (G₀ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (h : S2 → Real) (p : S2) (d : OpenPartialHomeomorph E2 S2)
    {scale delta r : Real} (hscale : 0 < scale) (hdelta : 0 < delta)
    (hGheight : ∀ q : S2, G₀ q 2 =
      scale * (h q - h p))
    (hDheight : ∀ y : E3, D y 2 = y 2)
    (F : Fin 2 → Real × Real → S2) (a₀ b₀ : Fin 2 → Real)
    (A B : Fin 2 → Real → Real)
    (hzero : ∀ i, A i 0 = a₀ i ∧ B i 0 = b₀ i)
    (hcontinuous : ∀ u ∈ Icc (-delta) delta, ∀ i,
      ContinuousAt (A i) u ∧ ContinuousAt (B i) u)
    (hrecut : ∀ u ∈ Icc (-delta) delta,
      (h ⁻¹' {h p + u}) \ d '' openSquare r =
        ⋃ i, F i '' (Icc (A i u) (B i u) ×ˢ ({u} : Set Real))) :
    let G := G₀.trans D
    let Aphysical : Fin 2 → Real → Real := fun i t => A i (t / scale)
    let Bphysical : Fin 2 → Real → Real := fun i t => B i (t / scale)
    0 < scale * delta ∧
      (∀ i, Aphysical i 0 = a₀ i ∧ Bphysical i 0 = b₀ i) ∧
      ∀ t ∈ Icc (-(scale * delta)) (scale * delta),
        (∀ i, ContinuousAt (Aphysical i) t ∧ ContinuousAt (Bphysical i) t) ∧
        (⋃ i, (fun z => toE2 (G (F i (z, t / scale)))) ''
          Icc (Aphysical i t) (Bphysical i t)) =
          {x : E2 | toE3 x t ∈ G '' sphere (0 : E3) 1} \
            {x : E2 | toE3 x t ∈ (fun q : S2 => G q) '' (d '' openSquare r)} := by
  refine ⟨mul_pos hscale hdelta, ?_, ?_⟩
  · intro i
    simpa using hzero i
  · intro t ht
    have hu : t / scale ∈ Icc (-delta) delta := by
      constructor
      · apply (le_div_iff₀ hscale).mpr
        nlinarith [ht.1]
      · apply (div_le_iff₀ hscale).mpr
        nlinarith [ht.2]
    refine ⟨?_, ?_⟩
    · intro i
      exact ⟨(hcontinuous _ hu i).1.comp (f := fun u : Real => u / scale)
          (continuous_id.div_const scale).continuousAt,
        (hcontinuous _ hu i).2.comp (f := fun u : Real => u / scale)
          (continuous_id.div_const scale).continuousAt⟩
    · have hheight (q : S2) : (G₀.trans D) q 2 = scale * (h q - h p) := by
        change D (G₀ q) 2 = _
        rw [hDheight, hGheight]
      have heq := projected_model_recut_strips (G₀.trans D) h p d hscale hheight
        F (fun i => A i (t / scale)) (fun i => B i (t / scale)) (hrecut _ hu)
      have hscaled : scale * (t / scale) = t := by
        field_simp
      simpa only [hscaled] using heq

private theorem physical_projected_nested_recut_strips
    (T D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (p : S2) (d : OpenPartialHomeomorph E2 S2)
    {scale delta r : Real} (hscale : 0 < scale) (hdelta : 0 < delta)
    (hGheight : ∀ q : S2, T (shear (3 / 10) q) 2 =
      scale * (height q - height p))
    (hDheight : ∀ y : E3, D y 2 = y 2)
    (F : Fin 2 → Real × Real → S2) (a₀ b₀ : Fin 2 → Real)
    (A B : Fin 2 → Real → Real)
    (hzero : ∀ i, A i 0 = a₀ i ∧ B i 0 = b₀ i)
    (hcontinuous : ∀ u ∈ Icc (-delta) delta, ∀ i,
      ContinuousAt (A i) u ∧ ContinuousAt (B i) u)
    (hrecut : ∀ u ∈ Icc (-delta) delta,
      (height ⁻¹' {height p + u}) \ d '' openSquare r =
        ⋃ i, F i '' (Icc (A i u) (B i u) ×ˢ ({u} : Set Real))) :
    let G₀ := (shear (3 / 10)).trans T
    let G := G₀.trans D
    let Aphysical : Fin 2 → Real → Real := fun i t => A i (t / scale)
    let Bphysical : Fin 2 → Real → Real := fun i t => B i (t / scale)
    0 < scale * delta ∧
      (∀ i, Aphysical i 0 = a₀ i ∧ Bphysical i 0 = b₀ i) ∧
      ∀ t ∈ Icc (-(scale * delta)) (scale * delta),
        (∀ i, ContinuousAt (Aphysical i) t ∧ ContinuousAt (Bphysical i) t) ∧
        (⋃ i, (fun z => toE2 (G (F i (z, t / scale)))) ''
          Icc (Aphysical i t) (Bphysical i t)) =
          {x : E2 | toE3 x t ∈ G '' sphere (0 : E3) 1} \
            {x : E2 | toE3 x t ∈ (fun q : S2 => G q) '' (d '' openSquare r)} := by
  exact physical_projected_recut_model_strips ((shear (3 / 10)).trans T) D
    height p d hscale hdelta hGheight hDheight F a₀ b₀ A B hzero hcontinuous hrecut

end ModelConstruction

section SetSlab

private theorem image_exterior_of_level_matching
    {X : Type*} (Q : X ≃ X) (C L L' S S' : Set X)
    (hfix : EqOn Q id C) (hlevel : Q '' L = L')
    (houtside : L \ C = S \ C) (houtside' : L' \ C = S' \ C)
    (hinside : S ∩ C = S' ∩ C) : Q '' S = S' := by
  have hC : Q '' C = C := hfix.image_eq.trans (image_id _)
  have hout : Q '' (S \ C) = S' \ C := by
    rw [← houtside, image_sdiff Q.injective, hlevel, hC, houtside']
  have hin : Q '' (S ∩ C) = S' ∩ C :=
    ((hfix.mono inter_subset_right).image_eq.trans (image_id _)).trans hinside
  calc
    Q '' S = Q '' ((S \ C) ∪ (S ∩ C)) :=
      congrArg (fun A : Set X => Q '' A) (sdiff_union_inter S C).symm
    _ = Q '' (S \ C) ∪ Q '' (S ∩ C) := image_union _ _ _
    _ = (S' \ C) ∪ (S' ∩ C) := by rw [hout, hin]
    _ = S' := sdiff_union_inter S' C

private theorem image_sdiff_of_relative_matching
    {X : Type*} (Q : X ≃ X) (C S S' P : Set X)
    (hfix : EqOn Q id C) (hmatch : Q '' S = S') (hPC : P ⊆ C) :
    Q '' (S \ P) = S' \ P := by
  have hP : Q '' P = P := (hfix.mono hPC).image_eq.trans (image_id _)
  rw [image_sdiff Q.injective, hmatch, hP]

private def arcPairTrace (l u : Fin 2 → Real) (mu : Fin 2 → Real × Real → E2)
    (t : Real) : Set E2 :=
  ⋃ i, (fun s => mu i (t, s)) '' Icc (l i) (u i)

private theorem exists_relative_set_slab_of_regular_level_matching
    {eta : Real} (heta : 0 < eta)
    (l l₀ l₁ u₁ u₀ u : Fin 2 → Real)
    (hll₀ : ∀ i, l i ≤ l₀ i) (hl₀l₁ : ∀ i, l₀ i < l₁ i)
    (hl₁u₁ : ∀ i, l₁ i ≤ u₁ i) (hu₁u₀ : ∀ i, u₁ i < u₀ i)
    (hu₀u : ∀ i, u₀ i ≤ u i)
    (mu : Fin 2 → Real × Real → E2)
    (W : Fin 2 → Set (Real × Real)) (hW : ∀ i, IsOpen (W i))
    (hrect : ∀ i, Icc (-eta) eta ×ˢ Icc (l i) (u i) ⊆ W i)
    (hmu : ∀ i, ContDiffOn Real ∞ (mu i) (W i))
    (hinj : ∀ i t, t ∈ Icc (-eta) eta →
      InjOn (fun s => mu i (t, s)) (Icc (l i) (u i)))
    (hder : ∀ i t, t ∈ Icc (-eta) eta → ∀ s ∈ Icc (l i) (u i),
      deriv (fun y => mu i (t, y)) s ≠ 0)
    (hstationary : ∀ i t, t ∈ Icc (-eta) eta →
      ∀ s ∈ Icc (l i) (l₁ i) ∪ Icc (u₁ i) (u i),
        mu i (t, s) = mu i (0, s))
    (hdisj : Pairwise (fun i j =>
      Disjoint (mu i '' (({0} : Set Real) ×ˢ Icc (l i) (u i)))
        (mu j '' (({0} : Set Real) ×ˢ Icc (l j) (u j)))))
    (C : Set E2) (hC : IsClosed C)
    (havoid : ∀ i s, s ∈ Icc (l₁ i) (u₁ i) → mu i (0, s) ∉ C)
    (La Lm : Real → Set E2)
    (hsource : ∀ t ∈ Icc (-eta) eta, La t \ C = La 0 \ C)
    (hmodel : ∀ t ∈ Icc (-eta) eta,
      Lm t \ C = arcPairTrace l u mu t \ C)
    (hcommon : ∀ t ∈ Icc (-eta) eta, La t ∩ C = Lm t ∩ C)
    (hregular : ∀ a ∈ Icc (-eta) eta, a < 0 →
      ∃ L : Set E2, IsCompact L ∧ Disjoint L C ∧
        ∃ Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          (∀ x, x ∉ L → Q x = x) ∧ Q '' La a = Lm a) :
    ∃ delta : Real, 0 < delta ∧ delta ≤ eta ∧
      ∃ K O : Set E2, IsCompact K ∧ IsOpen O ∧ C ⊆ O ∧ Disjoint K O ∧
        ∃ Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) ∧
          ContDiff Real ∞ (fun z : Real × E2 => (Phi z.1).symm z.2) ∧
          (∀ t x, x ∉ K → Phi t x = x) ∧
          (∀ t x, x ∈ O → Phi t x = x) ∧
          ∀ t ∈ Icc (-delta) delta,
            Phi t '' La t = Lm t ∧
            ∀ P ⊆ C, Phi t '' (La t \ P) = Lm t \ P := by
  obtain ⟨delta, hd, hdeta, K, O, hK, _, hCO, hKO, Psi, _, hPsi, _, hPsifix,
      _, hmove⟩ :=
    exists_relative_extension_of_central_arc_pair
      heta l l₀ l₁ u₁ u₀ u hll₀ hl₀l₁ hl₁u₁ hu₁u₀ hu₀u
      mu W hW hrect hmu hinj hder hstationary hdisj C hC havoid
  have htime {t : Real} (ht : t ∈ Icc (-delta) delta) : t ∈ Icc (-eta) eta :=
    ⟨by linarith [ht.1], ht.2.trans hdeta⟩
  let a : Real := -(delta / 2)
  have ha : a ∈ Icc (-delta) delta := ⟨by dsimp [a]; linarith, by dsimp [a]; linarith⟩
  have ha0 : a < 0 := by dsimp [a]; linarith
  obtain ⟨L, hL, hLC, Q, hQfix, hQlevel⟩ := hregular a (htime ha) ha0
  have hQC : EqOn Q id C := by
    intro x hx
    exact hQfix x (fun hxL => Set.disjoint_left.mp hLC hxL hx)
  have htrace (t : Real) (ht : t ∈ Icc (-delta) delta) :
      Psi t '' arcPairTrace l u mu 0 = arcPairTrace l u mu t := by
    simp only [arcPairTrace, image_iUnion, image_image]
    apply iUnion_congr
    intro i
    exact image_congr (fun s hs => hmove i t ht s hs)
  have hinverse : (Psi a).symm '' arcPairTrace l u mu a = arcPairTrace l u mu 0 := by
    rw [← htrace a ha]
    exact Equiv.symm_image_image (Psi a).toEquiv _
  let Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
    fun t => (Q.trans (Psi a).symm).trans (Psi t)
  have hPhi : ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) :=
    hPsi.comp (contDiff_fst.prodMk
      (((Q.trans (Psi a).symm).contMDiff.contDiff).comp contDiff_snd))
  have hPhifix (t : Real) (x : E2) (hx : x ∉ K ∪ L) : Phi t x = x := by
    have hxK : x ∉ K := fun h => hx (Or.inl h)
    have hxL : x ∉ L := fun h => hx (Or.inr h)
    have hinv : (Psi a).symm x = x := by
      apply (Psi a).injective
      exact ((Psi a).apply_symm_apply x).trans (hPsifix a x hxK).symm
    change Psi t ((Psi a).symm (Q x)) = x
    rw [hQfix x hxL, hinv, hPsifix t x hxK]
  have hKC : Disjoint K C := hKO.mono_right hCO
  have hprotected : C ⊆ (K ∪ L)ᶜ := by
    intro x hx hmem
    rcases hmem with hxK | hxL
    · exact Set.disjoint_left.mp hKC hxK hx
    · exact Set.disjoint_left.mp hLC hxL hx
  have hPhiC (t : Real) : EqOn (Phi t) id C :=
    fun x hx => hPhifix t x (hprotected hx)
  have hPsiC (t : Real) : EqOn (Psi t) id C := by
    intro x hx
    exact hPsifix t x (fun hxK => Set.disjoint_left.mp hKC hxK hx)
  have hPsiInvC : EqOn (Psi a).symm id C := by
    intro x hx
    apply (Psi a).injective
    exact ((Psi a).apply_symm_apply x).trans (hPsiC a hx).symm
  have hmatch (t : Real) (ht : t ∈ Icc (-delta) delta) :
      Phi t '' La t = Lm t := by
    have hQout : Q '' (La t \ C) = arcPairTrace l u mu a \ C := by
      rw [hsource t (htime ht), ← hsource a (htime ha)]
      exact (image_sdiff_of_relative_matching Q.toEquiv C (La a) (Lm a) C
        hQC hQlevel Subset.rfl).trans (hmodel a (htime ha))
    have hout : Phi t '' (La t \ C) = Lm t \ C := by
      change ((Psi t) ∘ (Psi a).symm ∘ Q) '' (La t \ C) = _
      rw [image_comp, image_comp, hQout]
      have hstep : (Psi a).symm '' (arcPairTrace l u mu a \ C) =
          arcPairTrace l u mu 0 \ C :=
        image_sdiff_of_relative_matching (Psi a).symm.toEquiv C
          (arcPairTrace l u mu a) (arcPairTrace l u mu 0) C hPsiInvC hinverse Subset.rfl
      have hstep' : Psi t '' (arcPairTrace l u mu 0 \ C) =
          arcPairTrace l u mu t \ C :=
        image_sdiff_of_relative_matching (Psi t).toEquiv C
          (arcPairTrace l u mu 0) (arcPairTrace l u mu t) C (hPsiC t)
          (htrace t ht) Subset.rfl
      rw [hstep, hstep']
      exact (hmodel t (htime ht)).symm
    have hin : Phi t '' (La t ∩ C) = Lm t ∩ C :=
      (((hPhiC t).mono inter_subset_right).image_eq.trans (image_id _)).trans
        (hcommon t (htime ht))
    calc
      Phi t '' La t = Phi t '' ((La t \ C) ∪ (La t ∩ C)) := by
        rw [sdiff_union_inter]
      _ = Lm t := by rw [image_union, hout, hin, sdiff_union_inter]
  refine ⟨delta, hd, hdeta, K ∪ L, (K ∪ L)ᶜ,
    hK.union hL, (hK.union hL).isClosed.isOpen_compl, hprotected,
    disjoint_compl_right, Phi, hPhi,
    Poincare.Manifold.Schoenflies.Plane.Isotopy.ArcPairs.contDiff_family_symm Phi hPhi,
    hPhifix, fun t x hx => hPhifix t x hx, ?_⟩
  intro t ht
  refine ⟨hmatch t ht, ?_⟩
  intro P hPC
  exact image_sdiff_of_relative_matching (Phi t).toEquiv C (La t)
    (Lm t) P (hPhiC t) (hmatch t ht) hPC

end SetSlab

section SlabMatching

open SaddleLevel Filter
open scoped _root_.Topology
set_option backward.isDefEq.respectTransparency false

private theorem exists_nested_chart_and_common_neighborhood
    (g : S2 → E3) (hg : Continuous g) (hginj : Injective g)
    (e d : OpenPartialHomeomorph E2 S2) (p : S2)
    (hp : 1 < height p) (hd0 : 0 ∈ d.source) (hdp : d 0 = p)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    (T : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    {scale ρ r : Real} (hscale : 0 < scale) (hρ : 0 < ρ)
    (hr : 0 < r) (hrρ : 2 * r < ρ)
    (hsource : closedBall (0 : E2) ρ ⊆ d.source)
    (he : ∀ x ∈ closedBall (0 : E2) ρ, Real.sqrt scale • x ∈ e.source)
    (hactual : ∀ x ∈ e.source, g (e x) 2 = -(x 0)^2 + (x 1)^2)
    (hheight : ∀ q : S2, T (shear (3 / 10) q) 2 =
      scale * (height q - height p))
    (hmatch : ∀ x ∈ closedBall (0 : E2) ρ,
      T (shear (3 / 10) (d x)) = g (e (Real.sqrt scale • x))) :
    mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0 ∧
      (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8) ∧
      ∃ d' : OpenPartialHomeomorph E2 S2,
        0 ∈ d'.source ∧ d' 0 = p ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ d' d'.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ d'.symm d'.target ∧
        closedSquare r ⊆ d'.source ∧
        (∀ x ∈ d'.source, height (d' x) = height p - (x 0)^2 + (x 1)^2) ∧
        (∀ x, d' x = d x) ∧
        ∃ U : Set E3, IsOpen U ∧
          (fun q : S2 => T (shear (3 / 10) q)) '' (d' '' closedSquare r) ⊆ U ∧
          (((shear (3 / 10)).trans T) '' sphere (0 : E3) 1) ∩ U = range g ∩ U := by
  let G₀ := (shear (3 / 10)).trans T
  have haxis (y : E3) : inner Real (EuclideanSpace.single 2 1 : E3) y = y 2 := by
    simp [PiLp.inner_apply]
  obtain ⟨hform, hcritical, _, hlatitude, _, _⟩ := critical_fiber_geometry_of_matching
    g (EuclideanSpace.single 2 1) 0 e d p hp hd0 hdp hd hdi G₀ hscale hρ he
    (by intro x hx; simpa only [haxis, zero_sub] using hactual x hx)
    (by intro q; rw [haxis, zero_add]; exact hheight q) hmatch
  obtain ⟨he0, hep, he', hei, hers, heform, heq⟩ :=
    restricted_nested_morse_chart d p hdp hd hdi hρ hr.le hrρ hsource hform
  obtain ⟨U, hU, hQU, hcommon⟩ := exists_common_neighborhood_for_model_square
    hg hginj e d G₀ hscale hr.le hrρ hsource he hmatch
  exact ⟨hcritical, hlatitude, d.restrOpen (ball (0 : E2) ρ) isOpen_ball,
    he0, hep, he', hei, hers, heform, heq, U, hU, hQU, hcommon⟩

private theorem vertical_strip_union_eq_planar_slice
    (gamma : Fin 2 → Real → E3) (a b : Fin 2 → Real)
    (hzero : ∀ i s, s ∈ Icc (a i) (b i) → gamma i s 2 = 0) (t : Real) :
    (⋃ i, (fun s => gamma i s + t • (EuclideanSpace.single 2 1 : E3)) ''
      Icc (a i) (b i)) =
      slice (⋃ i, (fun s => toE2 (gamma i s)) '' Icc (a i) (b i)) t := by
  have hproj (i : Fin 2) (s : Real) :
      toE2 (gamma i s + t • (EuclideanSpace.single 2 1 : E3)) =
        toE2 (gamma i s) := by
    ext k
    fin_cases k <;> simp [toE2]
  ext y
  constructor
  · intro hy
    obtain ⟨i, s, hs, rfl⟩ := mem_iUnion.mp hy
    refine ⟨?_, ?_⟩
    · rw [hproj]
      exact mem_iUnion_of_mem i (mem_image_of_mem _ hs)
    · simp [hzero i s hs]
  · rintro ⟨hyproj, hyheight⟩
    obtain ⟨i, s, hs, heq⟩ := mem_iUnion.mp hyproj
    refine mem_iUnion_of_mem i ⟨s, hs, ?_⟩
    ext k
    fin_cases k
    · exact congrArg (fun z : E2 => z 0) ((hproj i s).trans heq)
    · exact congrArg (fun z : E2 => z 1) ((hproj i s).trans heq)
    · simpa [hzero i s hs] using hyheight.symm

private theorem actual_moving_cuts_and_whole_level_of_flattening
    {X : Type*} (g : X → E3) (hginj : Function.Injective g)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ y : E3, D y 2 = y 2)
    (e : E2 → X) (r : Real) (F : Fin 2 → Real × Real → X)
    (a b : Fin 2 → Real) {eta : Real} (A B : Fin 2 → Real → Real)
    (hzero : ∀ i s, s ∈ Icc (a i) (b i) → g (F i (s, 0)) 2 = 0)
    (hflat : ∀ i t, t ∈ Icc (-eta) eta → ∀ s ∈ Icc (a i) (b i),
      D (g (F i (s, t))) = g (F i (s, 0)) + t • (EuclideanSpace.single 2 1 : E3))
    (hcuts : ∀ i t, t ∈ Icc (-eta) eta →
      a i ≤ A i t ∧ B i t ≤ b i)
    (hexterior : ∀ t ∈ Icc (-eta) eta,
      (D ∘ g) '' ({q : X | g q 2 = t} \ e '' openSquare r) =
        ⋃ i, (fun s => g (F i (s, 0)) + t • (EuclideanSpace.single 2 1 : E3)) ''
          Icc (A i t) (B i t)) :
    let P : Set E3 := (D ∘ g) '' (e '' openSquare r)
    let S : Set E2 := ⋃ i, (fun s => toE2 (g (F i (s, 0)))) '' Icc (a i) (b i)
    ∀ t ∈ Icc (-eta) eta,
      ({x : E2 | toE3 x t ∈ range (D ∘ g)} \
          {x : E2 | toE3 x t ∈ P}) =
        ⋃ i, (fun s => toE2 (g (F i (s, 0)))) '' Icc (A i t) (B i t) ∧
      range (D ∘ g) ∩ {y : E3 | y 2 = t} =
        (P ∩ {y : E3 | y 2 = t}) ∪ slice S t := by
  dsimp only
  let G : X → E3 := D ∘ g
  let P : Set E3 := G '' (e '' openSquare r)
  let gamma : Fin 2 → Real → E3 := fun i s => g (F i (s, 0))
  have hGinj : Function.Injective G := D.injective.comp hginj
  have hlevel (t : Real) : G '' {q : X | g q 2 = t} =
      range G ∩ {y : E3 | y 2 = t} := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, rfl⟩, (hDheight _).trans hq⟩
    · rintro ⟨⟨q, rfl⟩, hq⟩
      refine ⟨q, ?_, rfl⟩
      exact (hDheight _).symm.trans hq
  intro t ht
  have hsub (i : Fin 2) : Icc (A i t) (B i t) ⊆ Icc (a i) (b i) :=
    Icc_subset_Icc (hcuts i t ht).1 (hcuts i t ht).2
  have hzero_cut (i : Fin 2) (s : Real) (hs : s ∈ Icc (A i t) (B i t)) :
      gamma i s 2 = 0 := hzero i s (hsub i hs)
  let R : Set E2 :=
    ⋃ i, (fun s => toE2 (gamma i s)) '' Icc (A i t) (B i t)
  have hspatial : (range G ∩ {y : E3 | y 2 = t}) \ P = slice R t := by
    calc
      _ = G '' ({q : X | g q 2 = t} \ e '' openSquare r) := by
        rw [image_sdiff hGinj, hlevel]
      _ = ⋃ i, (fun s => gamma i s + t • (EuclideanSpace.single 2 1 : E3)) ''
          Icc (A i t) (B i t) := hexterior t ht
      _ = slice R t := vertical_strip_union_eq_planar_slice gamma
        (fun i => A i t) (fun i => B i t) hzero_cut t
  have hcoord (x : E2) : toE2 (toE3 x t) = x := by
    ext i
    fin_cases i <;> rfl
  constructor
  · ext x
    have hx := Set.ext_iff.mp hspatial (toE3 x t)
    simpa only [Set.mem_sdiff, mem_inter_iff, mem_ofPred_eq, slice, hcoord,
      show toE3 x t 2 = t from rfl, and_true] using hx
  · ext y
    constructor
    · rintro ⟨hyG, hyheight⟩
      by_cases hyP : y ∈ P
      · exact Or.inl ⟨hyP, hyheight⟩
      · have hyR := hspatial.subset ⟨⟨hyG, hyheight⟩, hyP⟩
        refine Or.inr ⟨?_, hyR.2⟩
        obtain ⟨i, s, hs, heq⟩ := mem_iUnion.mp hyR.1
        exact mem_iUnion_of_mem i ⟨s, hsub i hs, heq⟩
    · rintro (⟨hyP, hyheight⟩ | hyS)
      · obtain ⟨q, _, hq⟩ := hyP
        exact ⟨⟨q, hq⟩, hyheight⟩
      · have hyheight := hyS.2
        have hfull := (vertical_strip_union_eq_planar_slice gamma a b hzero t).superset hyS
        obtain ⟨i, s, hs, heq⟩ := mem_iUnion.mp hfull
        exact ⟨⟨F i (s, t), (hflat i t ht s hs).trans heq⟩, hyheight⟩

private theorem exists_common_open_neighborhood_of_compact_slices
    {T X Y : Type*} [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]
    {I : Set T} {C : Set X} (hI : IsCompact I) (hC : IsCompact C)
    {U : Set Y} (hU : IsOpen U) (lift : T × X → Y) (hlift : Continuous lift)
    {Nreg : Set X} (hNreg : IsOpen Nreg) (hCNreg : C ⊆ Nreg)
    (hinside : ∀ t ∈ I, ∀ x ∈ C, lift (t, x) ∈ U) :
    ∃ N : Set X, IsOpen N ∧ C ⊆ N ∧ N ⊆ Nreg ∧
      ∀ t ∈ I, ∀ x ∈ N, lift (t, x) ∈ U := by
  have hprod : I ×ˢ C ⊆ lift ⁻¹' U := by
    intro z hz
    exact hinside z.1 hz.1 z.2 hz.2
  obtain ⟨V, W, _, hW, hIV, hCW, hVW⟩ :=
    generalized_tube_lemma hI hC (hU.preimage hlift) hprod
  refine ⟨W ∩ Nreg, hW.inter hNreg, fun x hx => ⟨hCW hx, hCNreg hx⟩,
    inter_subset_right, ?_⟩
  intro t ht x hx
  exact hVW ⟨hIV ht, hx.1⟩

private def planarFiber (Z : Set E3) (t : Real) : Set E2 := {x | toE3 x t ∈ Z}

private def flattenedSphereMap (G₀ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (p : S2) : E3 := D (G₀ p)

theorem exists_relative_model_slab_transport_of_raw_model_strips
    (G₀ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ x : E3, D x 2 = x 2)
    (hDzero : ∀ x : E3, x 2 = 0 → D x = x)
    (h : S2 → Real) (c : Real) (d : OpenPartialHomeomorph E2 S2)
    {r scale : Real} (hr : 0 < r) (hscale : 0 < scale)
    (hrs : closedSquare r ⊆ d.source)
    (hform : ∀ x ∈ d.source, h (d x) = c - x 0 ^ 2 + x 1 ^ 2)
    (Fm : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
    (v a₀ b₀ w : Fin 2 → Real)
    (hchain : ∀ i, v i < a₀ i ∧ a₀ i < b₀ i ∧ b₀ i < w i)
    (hFsource : ∀ i, Icc (v i) (w i) ×ˢ ({0} : Set Real) ⊆ (Fm i).source)
    (hF : ∀ i, ContMDiffOn 𝓘(Real, Real × Real) (𝓡 2) ∞ (Fm i) (Fm i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) 𝓘(Real, Real × Real) ∞ (Fm i).symm (Fm i).target)
    (hheight : ∀ i z, z ∈ (Fm i).source → h (Fm i z) = c + z.2)
    (hGheight : ∀ i z, z ∈ (Fm i).source → G₀ (Fm i z) 2 = scale * z.2)
    (hdisjoint : Pairwise (fun i j => Disjoint (Fm i).target (Fm j).target))
    (hcentral : (⋃ i, Fm i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
      (h ⁻¹' {c}) \ d '' openSquare r)
    (hends : ∀ i, range (fun j : Fin 2 × Fin 2 => d (contact r j)) ∩
      (Fm i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
        {Fm i (a₀ i, 0), Fm i (b₀ i, 0)})
    (g : S2 → E3) (hg : Continuous g) (hginj : Injective g)
    {U : Set E3} (hU : IsOpen U)
    (hcommon : (G₀ '' sphere (0 : E3) 1) ∩ U = range g ∩ U)
    (hQU : (fun p : S2 => G₀ p) '' (d '' closedSquare r) ⊆ U)
    (Fa : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
    (a b : Fin 2 → Real) {eta : Real} (heta : 0 < eta)
    (hFa : ∀ i, Ioo (a i) (b i) ×ˢ Ioo (-eta) eta ⊆ (Fa i).source)
    (hactualheight : ∀ i z, z ∈ Ioo (a i) (b i) ×ˢ Ioo (-eta) eta →
      g (Fa i z) 2 = z.2)
    (hflat : ∀ i x, x ∈ Icc (a i) (b i) → ∀ t ∈ Ioo (-eta) eta,
      D (g (Fa i (x, t))) =
        g (Fa i (x, 0)) + t • (EuclideanSpace.single 2 1 : E3))
    (j₀ j₁ : Fin 2 → Fin 2) (q₀ q₁ : Fin 2 → Real)
    (hq₀ : ∀ i, q₀ i ∈ Ioo (a (j₀ i)) (b (j₀ i)))
    (hq₁ : ∀ i, q₁ i ∈ Ioo (a (j₁ i)) (b (j₁ i)))
    (hcontact₀ : ∀ i, G₀ (Fm i (a₀ i, 0)) = g (Fa (j₀ i) (q₀ i, 0)))
    (hcontact₁ : ∀ i, G₀ (Fm i (b₀ i, 0)) = g (Fa (j₁ i) (q₁ i, 0)))
    (hcontactU₀ : ∀ i, G₀ (Fm i (a₀ i, 0)) ∈ U)
    (hcontactU₁ : ∀ i, G₀ (Fm i (b₀ i, 0)) ∈ U)
    (A B : Fin 2 → Real → Real)
    (hA : ∀ i, ContinuousAt (A i) 0) (hB : ∀ i, ContinuousAt (B i) 0)
    (hAzero : ∀ i, A i 0 = a₀ i) (hBzero : ∀ i, B i 0 = b₀ i)
    (hmodelcuts : ∀ t ∈ Icc (-eta) eta,
      (⋃ i, (fun x => toE2 (D (G₀ (Fm i (x, t / scale))))) '' Icc (A i t) (B i t)) =
        planarFiber ((G₀.trans D) '' sphere (0 : E3) 1) t \
          planarFiber (flattenedSphereMap G₀ D '' (d '' openSquare r)) t)
    (S : Set E2)
    (hactual : ∀ t ∈ Icc (-eta) eta,
      range (D ∘ g) ∩ {y : E3 | y 2 = t} =
        ((flattenedSphereMap G₀ D '' (d '' openSquare r)) ∩ {y : E3 | y 2 = t}) ∪ slice S t)
    (Nreg : Set E2) (hNreg : IsOpen Nreg)
    (hQNreg : toE2 '' ((flattenedSphereMap G₀ D '' (d '' closedSquare r)) ∩
      {y : E3 | y 2 = 0}) ⊆ Nreg) :
    ∃ (δ : Real) (C K O N : Set E2) (V : Set E3),
      0 < δ ∧ δ ≤ eta ∧ IsCompact C ∧ C ⊆ Nreg ∧ IsCompact K ∧ IsOpen O ∧
      C ⊆ O ∧ Disjoint K O ∧ IsOpen N ∧ C ⊆ N ∧ N ⊆ Nreg ∧ IsOpen V ∧
      flattenedSphereMap G₀ D '' (d '' closedSquare r) ⊆ V ∧
      (∀ t ∈ Icc (-δ) δ,
        planarFiber (flattenedSphereMap G₀ D '' (d '' closedSquare r)) t ⊆ C) ∧
      (∀ t ∈ Icc (-δ) δ, ∀ x, toE3 x t ∈ V → x ∈ C) ∧
      (∀ t ∈ Icc (-δ) δ,
        planarFiber (range (D ∘ g)) t \ C = planarFiber (range (D ∘ g)) 0 \ C) ∧
      (∀ t ∈ Icc (-δ) δ,
        planarFiber (range (D ∘ g)) t ∩ N =
          planarFiber ((G₀.trans D) '' sphere (0 : E3) 1) t ∩ N) ∧
      ∃ Psi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Psi 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Psi z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Psi z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Psi t x = x) ∧
        (∀ t x, x ∈ O → Psi t x = x) ∧
        ∀ t ∈ Icc (-δ) δ,
          Psi t '' (planarFiber ((G₀.trans D) '' sphere (0 : E3) 1) 0 \ C) =
            planarFiber ((G₀.trans D) '' sphere (0 : E3) 1) t \ C := by
  classical
  have hsingle (i : Fin 2) := exists_stationary_model_arc_of_endpoint_contacts
    G₀ D hDheight hDzero (Fm i) (hF i) (hFi i) hscale (hGheight i)
    (hchain i).1 (hchain i).2.1 (hchain i).2.2
    (fun x hx => hFsource i ⟨Ioo_subset_Icc_self hx, rfl⟩)
    g hg hginj hU hcommon Fa a b heta hFa hactualheight hflat
    (j₀ i) (j₁ i) (q₀ i) (q₁ i) (hq₀ i) (hq₁ i)
    (hcontact₀ i) (hcontact₁ i) (hcontactU₀ i) (hcontactU₁ i)
  choose l l₀ l₁ u₁ u₀ u d₁ J hcollars hd₁ hd₁eta hJ hJsub
    R hRzero hR hRinv hRfix W hW hrect hmu hmuinj hmuder hmu0 hmusource
    hstationary hendmatch using hsingle
  let mu : Fin 2 → Real × Real → E2 :=
    fun i z => toE2 (D (G₀ (Fm i (R i z.1 z.2, z.1 / scale))))
  let H : S2 → E3 := flattenedSphereMap G₀ D
  let Qclosed := H '' (d '' closedSquare r)
  let Qopen := H '' (d '' openSquare r)
  let Za := range (D ∘ g)
  let Zm := (G₀.trans D) '' sphere (0 : E3) 1
  let La : Real → Set E2 := planarFiber Za
  let Lm : Real → Set E2 := planarFiber Zm
  let Pm : Real → Set E2 := planarFiber Qopen
  have hHcont : Continuous H := D.continuous.comp (G₀.continuous.comp continuous_subtype_val)
  have hHinj : Injective H := D.injective.comp (G₀.injective.comp Subtype.val_injective)
  have hHzero (i : Fin 2) (x : Real) (hx : x ∈ Icc (v i) (w i)) : H (Fm i (x, 0)) 2 = 0 := by
    change D (G₀ (Fm i (x, 0))) 2 = 0
    rw [hDheight, hGheight i _ (hFsource i
      (show (x, 0) ∈ Icc (v i) (w i) ×ˢ ({0} : Set Real) from ⟨hx, rfl⟩)), mul_zero]
  have hlv (i : Fin 2) : v i < l i := (hcollars i).1
  have huw (i : Fin 2) : u i < w i := (hcollars i).2.2.2.2.2.2.2.2
  have hlu (i : Fin 2) : l i < u i := by
    rcases hcollars i with ⟨_, h₁, h₂, h₃, h₄, h₅, h₆, h₇, _⟩
    linarith
  have hsource (i : Fin 2) : Icc (l i) (u i) ×ˢ ({0} : Set Real) ⊆ (Fm i).source :=
    (prod_mono (Icc_subset_Icc (hlv i).le (huw i).le) Subset.rfl).trans (hFsource i)
  have hzeroeq (i : Fin 2) (x : Real) : mu i (0, x) = toE2 (H (Fm i (x, 0))) := by
    simp only [mu, hRzero, zero_div, H, flattenedSphereMap]
  have hcentraldisj : Pairwise (fun i j =>
      Disjoint (mu i '' (({0} : Set Real) ×ˢ Icc (l i) (u i)))
        (mu j '' (({0} : Set Real) ×ˢ Icc (l j) (u j)))) := by
    have hdisj := pairwise_disjoint_reparametrized_central_planar_traces Fm l u
      hsource hdisjoint H hHinj
      (fun i x hx => hHzero i x (Icc_subset_Icc (hlv i).le (huw i).le hx))
      (fun i t x => R i t x) hRzero
    have himage (i : Fin 2) :
        mu i '' (({0} : Set Real) ×ˢ Icc (l i) (u i)) =
          (fun z : Real × Real => toE2 (H (Fm i (R i z.1 z.2, z.1)))) ''
            (({0} : Set Real) ×ˢ Icc (l i) (u i)) := by
      apply image_congr
      rintro ⟨t, x⟩ ⟨ht, _⟩
      have ht0 : t = 0 := ht
      subst t
      simp only [mu, H, flattenedSphereMap, zero_div]
    intro i j hij
    rw [himage, himage]
    exact hdisj hij
  have hmidcuts (i : Fin 2) : a₀ i < l₁ i ∧ l₁ i ≤ u₁ i ∧ u₁ i < b₀ i :=
    ⟨(hcollars i).2.2.2.1, (hcollars i).2.2.2.2.1.le, (hcollars i).2.2.2.2.2.1⟩
  obtain ⟨hQcompact, hBcompact, hQB⟩ := compact_middle_arcs_disjoint_projected_square
    d hr hrs hform Fm v w a₀ b₀ hchain hFsource hheight hdisjoint hcentral hends H hHcont hHinj
    (fun i x hx => hHzero i x (Icc_subset_Icc (hchain i).1.le (hchain i).2.2.le hx))
    l₁ u₁ hmidcuts
  have hQDU : Qclosed ⊆ D '' U := by
    rintro x ⟨p, hp, rfl⟩
    exact ⟨G₀ p, hQU ⟨p, hp, rfl⟩, rfl⟩
  let Ureg : Set E3 := (D '' U) ∩ ({y : E3 | y 2 ≠ 0} ∪ toE2 ⁻¹' Nreg)
  have hproj : Continuous toE2 := by
    apply ContDiff.continuous (n := ∞) (𝕜 := Real)
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff
  have hUreg : IsOpen Ureg :=
    (D.toHomeomorph.isOpenMap U hU).inter
      ((isClosed_eq (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).continuous
        continuous_const).isOpen_compl.union (hNreg.preimage hproj))
  have hQUreg : Qclosed ⊆ Ureg := by
    intro y hy
    refine ⟨hQDU hy, ?_⟩
    by_cases hy0 : y 2 = 0
    · exact Or.inr (hQNreg ⟨y, ⟨hy, hy0⟩, rfl⟩)
    · exact Or.inl hy0
  obtain ⟨ρ, C, O₀, V, hρ, hC, hO₀, hO₀C, _, hCB, hlift, hnear, hV, hQV, hVslice⟩ :=
    exists_protected_slab_neighborhood Qclosed hQcompact
      hUreg hQUreg
      (⋃ i, (fun x => toE2 (H (Fm i (x, 0)))) '' Icc (l₁ i) (u₁ i)) hBcompact hQB
  have hCNreg : C ⊆ Nreg := by
    intro x hx
    have hh := (hlift 0 ⟨by linarith, hρ.le⟩ x hx).2
    rcases hh with hnonzero | hmem
    · exact False.elim (hnonzero rfl)
    · have heq : toE2 (toE3 x 0) = x := by ext i; fin_cases i <;> rfl
      exact heq ▸ hmem
  let η := min eta (min ρ (min (d₁ 0) (d₁ 1)))
  have hη : 0 < η := lt_min heta (lt_min hρ (lt_min (hd₁ 0) (hd₁ 1)))
  have hηeta : η ≤ eta := min_le_left _ _
  have hηρ : η ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hηd (i : Fin 2) : η ≤ d₁ i := by
    have hh : η ≤ min (d₁ 0) (d₁ 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    fin_cases i
    · exact hh.trans (min_le_left _ _)
    · exact hh.trans (min_le_right _ _)
  have htime {t : Real} (ht : t ∈ Icc (-η) η) : t ∈ Icc (-eta) eta :=
    ⟨by linarith [ht.1], ht.2.trans hηeta⟩
  have htimeρ {t : Real} (ht : t ∈ Icc (-η) η) : t ∈ Icc (-ρ) ρ :=
    ⟨by linarith [ht.1], ht.2.trans hηρ⟩
  have htimed (i : Fin 2) {t : Real} (ht : t ∈ Icc (-η) η) : t ∈ Icc (-(d₁ i)) (d₁ i) :=
    ⟨by linarith [ht.1, hηd i], ht.2.trans (hηd i)⟩
  have hQopen : Qopen ⊆ Qclosed := image_mono (image_mono (openSquare_subset_closedSquare r))
  have hclosedC (t : Real) (ht : t ∈ Icc (-η) η) : planarFiber Qclosed t ⊆ C := by
    intro x hx
    have hh := hO₀C (hnear (toE3 x t) hx (htimeρ ht))
    have heq : toE2 (toE3 x t) = x := by ext i; fin_cases i <;> rfl
    exact heq ▸ hh
  have hPmC (t : Real) (ht : t ∈ Icc (-η) η) : Pm t ⊆ C :=
    fun _ hx => hclosedC t ht (hQopen hx)
  have hlevel (i : Fin 2) (t : Real) (ht : t ∈ Icc (-η) η)
      (x : Real) (hx : x ∈ Icc (l i) (u i)) : mu i (t, x) ∈ Lm t := by
    let p : S2 := Fm i (R i t x, t / scale)
    have hpheight : H p 2 = t := by
      change D (G₀ p) 2 = t
      rw [hDheight, hGheight i _ (hmusource i t (htimed i ht) x hx)]
      exact mul_div_cancel₀ t hscale.ne'
    have heq : toE3 (mu i (t, x)) t = H p := by
      ext k
      fin_cases k
      · rfl
      · rfl
      · exact hpheight.symm
    change toE3 (mu i (t, x)) t ∈ Zm
    rw [heq]
    exact ⟨p, p.property, rfl⟩
  obtain ⟨ε, hε, hεη, hexterior⟩ := exists_fixed_trace_exterior_of_moving_cuts
    hη l u A B hA hB
    (fun i => by rw [hAzero]; exact (hcollars i).2.1.trans (hcollars i).2.2.1)
    (fun i => by rw [hAzero, hBzero]; exact (hchain i).2.1)
    (fun i => by rw [hBzero]; exact (hcollars i).2.2.2.2.2.2.1.trans (hcollars i).2.2.2.2.2.2.2.1)
    R hRinv hRzero J hJ hRfix
    (fun i z => toE2 (D (G₀ (Fm i (z.2, z.1 / scale))))) Lm Pm C hPmC
    (fun t ht => hmodelcuts t (htime ht)) hlevel
  have htimeε {t : Real} (ht : t ∈ Icc (-ε) ε) : t ∈ Icc (-η) η :=
    ⟨by linarith [ht.1], ht.2.trans hεη⟩
  have hcommonD : Zm ∩ (D '' U) = Za ∩ (D '' U) := by
    have hGimage : Zm = D '' (G₀ '' sphere (0 : E3) 1) := by
      rw [image_image]
      rfl
    have hDi : Injective (fun x : E3 => D x) := D.injective
    change Zm ∩ (D '' U) = range (D ∘ g) ∩ (D '' U)
    rw [hGimage, ← image_inter hDi, hcommon, image_inter hDi, range_comp]
  have hcommonC (t : Real) (ht : t ∈ Icc (-ε) ε) : La t ∩ C = Lm t ∩ C :=
    planar_level_inter_eq_of_common_spatial_patch hcommonD.symm
      (fun x hx => (hlift t (htimeρ (htimeε ht)) x hx).1)
  have hplaneLift : Continuous (fun z : Real × E2 => toE3 z.2 z.1) := by
    apply ContDiff.continuous (n := ∞) (𝕜 := Real)
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.comp contDiff_snd
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff.comp contDiff_snd
    · exact contDiff_fst
  obtain ⟨N, hN, hCN, hNNreg, hNlift⟩ :=
    exists_common_open_neighborhood_of_compact_slices
      (I := Icc (-ε) ε) isCompact_Icc hC (D.toHomeomorph.isOpenMap U hU)
      (fun z : Real × E2 => toE3 z.2 z.1) hplaneLift hNreg hCNreg
      (fun t ht x hx => (hlift t (htimeρ (htimeε ht)) x hx).1)
  have hcommonN (t : Real) (ht : t ∈ Icc (-ε) ε) : La t ∩ N = Lm t ∩ N :=
    planar_level_inter_eq_of_common_spatial_patch hcommonD.symm (hNlift t ht)
  have hsourceS (t : Real) (ht : t ∈ Icc (-ε) ε) : La t \ C = S \ C := by
    change planarFiber Za t \ C = _
    rw [show planarFiber Za t = toE2 '' (Za ∩ {y : E3 | y 2 = t}) from
      planar_level_eq_projected_height_slice Za t]
    exact projected_fiber_sdiff_eq_of_patch_union_slice (hactual t (htime (htimeε ht)))
      (fun _ hx => hQopen hx.1) (fun _ hx => hx.2)
      (fun y hy hytime => hO₀C (hnear y hy hytime)) (htimeρ (htimeε ht))
  have hsourceConst (t : Real) (ht : t ∈ Icc (-ε) ε) : La t \ C = La 0 \ C :=
    (hsourceS t ht).trans (hsourceS 0 ⟨by linarith, hε.le⟩).symm
  have havoid (i : Fin 2) (x : Real) (hx : x ∈ Icc (l₁ i) (u₁ i)) : mu i (0, x) ∉ C := by
    intro hxC
    exact disjoint_left.mp hCB hxC
      (mem_iUnion_of_mem i ⟨x, hx, (hzeroeq i x).symm⟩)
  obtain ⟨δ, hδ, hδε, K, O, hK, hO, hCO, hKO, Psi, hPsi0, hPsi, hPsiinv,
      hPsifix, hPsiO, hmove⟩ := exists_relative_extension_of_central_arc_pair
    hε l l₀ l₁ u₁ u₀ u
    (fun i => (hcollars i).2.1.le)
    (fun i => (hcollars i).2.2.1.trans (hcollars i).2.2.2.1)
    (fun i => (hcollars i).2.2.2.2.1.le)
    (fun i => (hcollars i).2.2.2.2.2.1.trans (hcollars i).2.2.2.2.2.2.1)
    (fun i => (hcollars i).2.2.2.2.2.2.2.1.le)
    mu W hW (fun i z hz => hrect i ⟨htimed i (htimeε hz.1), hz.2⟩) hmu
    (fun i t ht => hmuinj i t (htimed i (htimeε ht)))
    (fun i t ht => hmuder i t (htimed i (htimeε ht)))
    (fun i t ht => hstationary i t (htimed i (htimeε ht))) hcentraldisj
    C hC.isClosed havoid
  have htimeδ {t : Real} (ht : t ∈ Icc (-δ) δ) : t ∈ Icc (-ε) ε :=
    ⟨by linarith [ht.1], ht.2.trans hδε⟩
  have htrace (t : Real) (ht : t ∈ Icc (-δ) δ) :
      Psi t '' arcPairTrace l u mu 0 = arcPairTrace l u mu t := by
    simp only [arcPairTrace, image_iUnion, image_image]
    apply iUnion_congr
    intro i
    exact image_congr (fun s hs => hmove i t ht s hs)
  refine ⟨δ, C, K, O, N, V, hδ, hδε.trans (hεη.trans hηeta), hC, hCNreg, hK, hO,
    hCO, hKO, hN, hCN, hNNreg, hV, hQV, ?_, ?_, ?_, ?_,
    Psi, hPsi0, hPsi, hPsiinv, hPsifix, hPsiO, ?_⟩
  · intro t ht
    exact hclosedC t (htimeε (htimeδ ht))
  · intro t ht x hx
    exact hO₀C (hVslice t (htimeρ (htimeε (htimeδ ht))) x hx)
  · intro t ht
    exact hsourceConst t (htimeδ ht)
  · intro t ht
    exact hcommonN t (htimeδ ht)
  · intro t ht
    change Psi t '' (Lm 0 \ C) = Lm t \ C
    rw [(hexterior 0 ⟨by linarith, hε.le⟩).2.2.2,
      (hexterior t (htimeδ ht)).2.2.2]
    exact image_sdiff_of_relative_matching (Psi t).toEquiv C
      (arcPairTrace l u mu 0) (arcPairTrace l u mu t) C
      (fun x hx => hPsiO t x (hCO hx)) (htrace t ht) Subset.rfl

private theorem exists_relative_matching_of_model_transport
    {δ : Real} (hδ : 0 < δ) (C K O : Set E2)
    (hK : IsCompact K) (hCO : C ⊆ O) (hKO : Disjoint K O)
    (La Lm : Real → Set E2)
    (hsource : ∀ t ∈ Icc (-δ) δ, La t \ C = La 0 \ C)
    (hcommonC : ∀ t ∈ Icc (-δ) δ, La t ∩ C = Lm t ∩ C)
    (Psi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hPsi : ContDiff Real ∞ (fun z : Real × E2 => Psi z.1 z.2))
    (hPsifix : ∀ t x, x ∉ K → Psi t x = x)
    (hmove : ∀ t ∈ Icc (-δ) δ, Psi t '' (Lm 0 \ C) = Lm t \ C)
    (hregular : ∀ a ∈ Icc (-δ) δ, a < 0 →
      ∃ L : Set E2, IsCompact L ∧ Disjoint L C ∧
        ∃ Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          (∀ x, x ∉ L → Q x = x) ∧ Q '' La a = Lm a) :
    ∃ K' O' : Set E2, IsCompact K' ∧ IsOpen O' ∧ C ⊆ O' ∧ Disjoint K' O' ∧
      ∃ Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Phi z.1).symm z.2) ∧
        (∀ t x, x ∉ K' → Phi t x = x) ∧
        (∀ t x, x ∈ O' → Phi t x = x) ∧
        ∀ t ∈ Icc (-δ) δ,
          Phi t '' La t = Lm t ∧
          ∀ P ⊆ C, Phi t '' (La t \ P) = Lm t \ P := by
  classical
  let a' : Real := -(δ / 2)
  have ha : a' ∈ Icc (-δ) δ := ⟨by dsimp [a']; linarith, by dsimp [a']; linarith⟩
  have ha0 : a' < 0 := by dsimp [a']; linarith
  obtain ⟨L, hL, hLC, Q, hQfix, hQlevel⟩ :=
    hregular a' ha ha0
  have hQC : EqOn Q id C := by
    intro x hx
    exact hQfix x (fun hxL => Set.disjoint_left.mp hLC hxL hx)
  have hinverse : (Psi a').symm '' (Lm a' \ C) = Lm 0 \ C := by
    rw [← hmove a' ha]
    exact Equiv.symm_image_image (Psi a').toEquiv _
  let Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
    fun t => (Q.trans (Psi a').symm).trans (Psi t)
  have hPhi : ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) :=
    hPsi.comp (contDiff_fst.prodMk
      (((Q.trans (Psi a').symm).contMDiff.contDiff).comp contDiff_snd))
  have hPhifix (t : Real) (x : E2) (hx : x ∉ K ∪ L) : Phi t x = x := by
    have hxK : x ∉ K := fun h => hx (Or.inl h)
    have hxL : x ∉ L := fun h => hx (Or.inr h)
    have hinv : (Psi a').symm x = x := by
      apply (Psi a').injective
      exact ((Psi a').apply_symm_apply x).trans (hPsifix a' x hxK).symm
    change Psi t ((Psi a').symm (Q x)) = x
    rw [hQfix x hxL, hinv, hPsifix t x hxK]
  have hKC : Disjoint K C := hKO.mono_right hCO
  have hprotected : C ⊆ (K ∪ L)ᶜ := by
    intro x hx hmem
    rcases hmem with hxK | hxL
    · exact Set.disjoint_left.mp hKC hxK hx
    · exact Set.disjoint_left.mp hLC hxL hx
  have hPhiC (t : Real) : EqOn (Phi t) id C :=
    fun x hx => hPhifix t x (hprotected hx)
  have hmatch (t : Real) (ht : t ∈ Icc (-δ) δ) : Phi t '' La t = Lm t := by
    have hQout : Q '' (La t \ C) = Lm a' \ C := by
      rw [hsource t ht, ← hsource a' ha]
      exact image_sdiff_of_relative_matching Q.toEquiv C (La a') (Lm a') C
        hQC hQlevel Subset.rfl
    have hout : Phi t '' (La t \ C) = Lm t \ C := by
      change ((Psi t) ∘ (Psi a').symm ∘ Q) '' (La t \ C) = _
      rw [image_comp, image_comp, hQout, hinverse]
      exact hmove t ht
    have hin : Phi t '' (La t ∩ C) = Lm t ∩ C :=
      (((hPhiC t).mono inter_subset_right).image_eq.trans (image_id _)).trans
        (hcommonC t ht)
    calc
      Phi t '' La t = Phi t '' ((La t \ C) ∪ (La t ∩ C)) := by
        rw [sdiff_union_inter]
      _ = Lm t := by rw [image_union, hout, hin, sdiff_union_inter]
  refine ⟨K ∪ L, (K ∪ L)ᶜ, hK.union hL, (hK.union hL).isClosed.isOpen_compl,
    hprotected, disjoint_compl_right, Phi, hPhi,
    Poincare.Manifold.Schoenflies.Plane.Isotopy.ArcPairs.contDiff_family_symm Phi hPhi,
    hPhifix, fun t x hx => hPhifix t x hx, ?_⟩
  intro t ht
  refine ⟨hmatch t ht, ?_⟩
  intro P hPC
  exact image_sdiff_of_relative_matching (Phi t).toEquiv C (La t)
    (Lm t) P (hPhiC t) (hmatch t ht) hPC

private theorem exists_relative_slab_of_raw_model_strips
    (G₀ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ x : E3, D x 2 = x 2)
    (hDzero : ∀ x : E3, x 2 = 0 → D x = x)
    (h : S2 → Real) (c : Real) (d : OpenPartialHomeomorph E2 S2)
    {r scale : Real} (hr : 0 < r) (hscale : 0 < scale)
    (hrs : closedSquare r ⊆ d.source)
    (hform : ∀ x ∈ d.source, h (d x) = c - x 0 ^ 2 + x 1 ^ 2)
    (Fm : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
    (v a₀ b₀ w : Fin 2 → Real)
    (hchain : ∀ i, v i < a₀ i ∧ a₀ i < b₀ i ∧ b₀ i < w i)
    (hFsource : ∀ i, Icc (v i) (w i) ×ˢ ({0} : Set Real) ⊆ (Fm i).source)
    (hF : ∀ i, ContMDiffOn 𝓘(Real, Real × Real) (𝓡 2) ∞ (Fm i) (Fm i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) 𝓘(Real, Real × Real) ∞ (Fm i).symm (Fm i).target)
    (hheight : ∀ i z, z ∈ (Fm i).source → h (Fm i z) = c + z.2)
    (hGheight : ∀ i z, z ∈ (Fm i).source → G₀ (Fm i z) 2 = scale * z.2)
    (hdisjoint : Pairwise (fun i j => Disjoint (Fm i).target (Fm j).target))
    (hcentral : (⋃ i, Fm i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
      (h ⁻¹' {c}) \ d '' openSquare r)
    (hends : ∀ i, range (fun j : Fin 2 × Fin 2 => d (contact r j)) ∩
      (Fm i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
        {Fm i (a₀ i, 0), Fm i (b₀ i, 0)})
    (g : S2 → E3) (hg : Continuous g) (hginj : Injective g)
    {U : Set E3} (hU : IsOpen U)
    (hcommon : (G₀ '' sphere (0 : E3) 1) ∩ U = range g ∩ U)
    (hQU : (fun p : S2 => G₀ p) '' (d '' closedSquare r) ⊆ U)
    (Fa : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
    (a b : Fin 2 → Real) {eta : Real} (heta : 0 < eta)
    (hFa : ∀ i, Ioo (a i) (b i) ×ˢ Ioo (-eta) eta ⊆ (Fa i).source)
    (hactualheight : ∀ i z, z ∈ Ioo (a i) (b i) ×ˢ Ioo (-eta) eta →
      g (Fa i z) 2 = z.2)
    (hflat : ∀ i x, x ∈ Icc (a i) (b i) → ∀ t ∈ Ioo (-eta) eta,
      D (g (Fa i (x, t))) =
        g (Fa i (x, 0)) + t • (EuclideanSpace.single 2 1 : E3))
    (j₀ j₁ : Fin 2 → Fin 2) (q₀ q₁ : Fin 2 → Real)
    (hq₀ : ∀ i, q₀ i ∈ Ioo (a (j₀ i)) (b (j₀ i)))
    (hq₁ : ∀ i, q₁ i ∈ Ioo (a (j₁ i)) (b (j₁ i)))
    (hcontact₀ : ∀ i, G₀ (Fm i (a₀ i, 0)) = g (Fa (j₀ i) (q₀ i, 0)))
    (hcontact₁ : ∀ i, G₀ (Fm i (b₀ i, 0)) = g (Fa (j₁ i) (q₁ i, 0)))
    (hcontactU₀ : ∀ i, G₀ (Fm i (a₀ i, 0)) ∈ U)
    (hcontactU₁ : ∀ i, G₀ (Fm i (b₀ i, 0)) ∈ U)
    (A B : Fin 2 → Real → Real)
    (hA : ∀ i, ContinuousAt (A i) 0) (hB : ∀ i, ContinuousAt (B i) 0)
    (hAzero : ∀ i, A i 0 = a₀ i) (hBzero : ∀ i, B i 0 = b₀ i)
    (hmodelcuts : ∀ t ∈ Icc (-eta) eta,
      (⋃ i, (fun x => toE2 (D (G₀ (Fm i (x, t / scale))))) '' Icc (A i t) (B i t)) =
        planarFiber ((G₀.trans D) '' sphere (0 : E3) 1) t \
          planarFiber (flattenedSphereMap G₀ D '' (d '' openSquare r)) t)
    (S : Set E2)
    (hactual : ∀ t ∈ Icc (-eta) eta,
      range (D ∘ g) ∩ {y : E3 | y 2 = t} =
        ((flattenedSphereMap G₀ D '' (d '' openSquare r)) ∩ {y : E3 | y 2 = t}) ∪ slice S t)
    (Nreg : Set E2) (hNreg : IsOpen Nreg)
    (hQNreg : toE2 '' ((flattenedSphereMap G₀ D '' (d '' closedSquare r)) ∩
      {y : E3 | y 2 = 0}) ⊆ Nreg)
    (hregular : ∀ (C N : Set E2), IsCompact C → IsOpen N → C ⊆ N → N ⊆ Nreg →
      ∀ ε : Real, 0 < ε → ε ≤ eta →
      (∀ t ∈ Icc (-ε) ε,
        planarFiber (range (D ∘ g)) t ∩ N =
          planarFiber ((G₀.trans D) '' sphere (0 : E3) 1) t ∩ N) →
      ∀ t ∈ Icc (-ε) ε, t < 0 →
        ∃ K : Set E2, IsCompact K ∧ Disjoint K C ∧
          ∃ Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
            (∀ x, x ∉ K → Q x = x) ∧
            Q '' planarFiber (range (D ∘ g)) t =
              planarFiber ((G₀.trans D) '' sphere (0 : E3) 1) t) :
    ∃ (δ : Real) (C K O : Set E2) (V : Set E3),
      0 < δ ∧ δ ≤ eta ∧ IsCompact C ∧ C ⊆ Nreg ∧ IsCompact K ∧ IsOpen O ∧
      C ⊆ O ∧ Disjoint K O ∧ IsOpen V ∧
      flattenedSphereMap G₀ D '' (d '' closedSquare r) ⊆ V ∧
      (∀ t ∈ Icc (-δ) δ,
        planarFiber (flattenedSphereMap G₀ D '' (d '' closedSquare r)) t ⊆ C) ∧
      ∃ Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Phi z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Phi t x = x) ∧
        (∀ t x, x ∈ O → Phi t x = x) ∧
        (∀ t ∈ Icc (-δ) δ, ∀ x, toE3 x t ∈ V → Phi t x = x) ∧
        ∀ t ∈ Icc (-δ) δ,
          Phi t '' planarFiber (range (D ∘ g)) t =
            planarFiber ((G₀.trans D) '' sphere (0 : E3) 1) t ∧
          ∀ P ⊆ C, Phi t '' (planarFiber (range (D ∘ g)) t \ P) =
            planarFiber ((G₀.trans D) '' sphere (0 : E3) 1) t \ P := by
  classical
  obtain ⟨δ, C, K, O, N, V, hδ, hδη, hC, hCNreg, hK, hO, hCO, hKO,
      hN, hCN, hNNreg, hV, hQV, hclosedC, hVC, hsource, hcommonN,
      Psi, hPsi0, hPsi, hPsiinv, hPsifix, hPsiO, hmove⟩ :=
    exists_relative_model_slab_transport_of_raw_model_strips G₀ D hDheight hDzero
      h c d hr hscale hrs hform Fm v a₀ b₀ w hchain hFsource hF hFi hheight
      hGheight hdisjoint hcentral hends g hg hginj hU hcommon hQU
      Fa a b heta hFa hactualheight hflat j₀ j₁ q₀ q₁ hq₀ hq₁
      hcontact₀ hcontact₁ hcontactU₀ hcontactU₁ A B hA hB hAzero hBzero
      hmodelcuts S hactual Nreg hNreg hQNreg
  have hcommonC (t : Real) (ht : t ∈ Icc (-δ) δ) :
      planarFiber (range (D ∘ g)) t ∩ C =
        planarFiber ((G₀.trans D) '' sphere (0 : E3) 1) t ∩ C := by
    have heq := congrArg (fun Z : Set E2 => Z ∩ C) (hcommonN t ht)
    simpa only [inter_assoc, inter_eq_self_of_subset_right hCN] using heq
  obtain ⟨K', O', hK', hO', hCO', hKO', Phi, hPhi, hPhiinv, hfix, hfixO, hmatch⟩ :=
    exists_relative_matching_of_model_transport hδ C K O hK hCO hKO
      (planarFiber (range (D ∘ g)))
      (planarFiber ((G₀.trans D) '' sphere (0 : E3) 1))
      hsource hcommonC Psi hPsi hPsifix hmove
      (hregular C N hC hN hCN hNNreg δ hδ hδη hcommonN)
  exact ⟨δ, C, K', O', V, hδ, hδη, hC, hCNreg, hK', hO', hCO', hKO',
    hV, hQV, hclosedC, Phi, hPhi, hPhiinv, hfix, hfixO,
    fun t ht x hx => hfixO t x (hCO' (hVC t ht x hx)), hmatch⟩

private def nestedSlabMap (T : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) :
    Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ :=
  (Poincare.Manifold.Schoenflies.Saddle.Nested.shear (3 / 10)).trans T

theorem exists_model_slab_transport_of_central_level
    (G₀ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ x : E3, D x 2 = x 2)
    (hDzero : ∀ x : E3, x 2 = 0 → D x = x)
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {p : S2} (hunique : ∀ q, h q = h p →
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q = p)
    (hconnected : IsPreconnected (h ⁻¹' {h p}))
    (d : OpenPartialHomeomorph E2 S2) (hd0 : 0 ∈ d.source) (hdp : d 0 = p)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    (hform : ∀ x ∈ d.source, h (d x) = h p - x 0 ^ 2 + x 1 ^ 2)
    {r scale : Real} (hr : 0 < r) (hscale : 0 < scale)
    (hrs : closedSquare r ⊆ d.source)
    (hGheight : ∀ q : S2, G₀ q 2 = scale * (h q - h p))
    (g : S2 → E3) (hg : Continuous g) (hginj : Injective g)
    (e : E2 → S2)
    (hmatch : ∀ x ∈ closedSquare r,
      G₀ (d x) = g (e (Real.sqrt scale • x)))
    {U : Set E3} (hU : IsOpen U)
    (hcommon : (G₀ '' sphere (0 : E3) 1) ∩ U = range g ∩ U)
    (hQU : g '' (e '' closedSquare (Real.sqrt scale * r)) ⊆ U)
    (Fa : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
    (a aa₀ ab₀ b : Fin 2 → Real)
    (hachain : ∀ i, a i < aa₀ i ∧ aa₀ i < ab₀ i ∧ ab₀ i < b i)
    (La : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2))
    (hLa : ∀ k, Fa k.1 (stripEndpoint aa₀ ab₀ k, 0) =
      e (contact (Real.sqrt scale * r) (La k)))
    {eta : Real} (heta : 0 < eta)
    (hFa : ∀ i, Ioo (a i) (b i) ×ˢ Ioo (-eta) eta ⊆ (Fa i).source)
    (hactualheight : ∀ i z, z ∈ Ioo (a i) (b i) ×ˢ Ioo (-eta) eta →
      g (Fa i z) 2 = z.2)
    (hflat : ∀ i x, x ∈ Icc (a i) (b i) → ∀ t ∈ Ioo (-eta) eta,
      D (g (Fa i (x, t))) =
        g (Fa i (x, 0)) + t • (EuclideanSpace.single 2 1 : E3))
    (S : Set E2)
    (hactual : ∀ t ∈ Icc (-eta) eta,
      range (D ∘ g) ∩ {y : E3 | y 2 = t} =
        (((D ∘ g) '' (e '' openSquare (Real.sqrt scale * r))) ∩
          {y : E3 | y 2 = t}) ∪ slice S t)
    (Nreg : Set E2) (hNreg : IsOpen Nreg)
    (hQNreg : toE2 '' (((D ∘ g) '' (e '' closedSquare (Real.sqrt scale * r))) ∩
      {y : E3 | y 2 = 0}) ⊆ Nreg) :
    ∃ (δ : Real) (C K O N : Set E2) (V : Set E3),
      0 < δ ∧ δ ≤ eta ∧ IsCompact C ∧ C ⊆ Nreg ∧ IsCompact K ∧ IsOpen O ∧
      C ⊆ O ∧ Disjoint K O ∧ IsOpen N ∧ C ⊆ N ∧ N ⊆ Nreg ∧ IsOpen V ∧
      (D ∘ g) '' (e '' closedSquare (Real.sqrt scale * r)) ⊆ V ∧
      (∀ t ∈ Icc (-δ) δ,
        planarFiber ((D ∘ g) '' (e '' closedSquare (Real.sqrt scale * r))) t ⊆ C) ∧
      (∀ t ∈ Icc (-δ) δ, ∀ x, toE3 x t ∈ V → x ∈ C) ∧
      (∀ t ∈ Icc (-δ) δ,
        planarFiber (range (D ∘ g)) t \ C = planarFiber (range (D ∘ g)) 0 \ C) ∧
      (∀ t ∈ Icc (-δ) δ,
        planarFiber (range (D ∘ g)) t ∩ N =
          planarFiber ((G₀.trans D) '' sphere (0 : E3) 1) t ∩ N) ∧
      ∃ Psi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Psi 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Psi z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Psi z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Psi t x = x) ∧
        (∀ t x, x ∈ O → Psi t x = x) ∧
        ∀ t ∈ Icc (-δ) δ,
          Psi t '' (planarFiber ((G₀.trans D) '' sphere (0 : E3) 1) 0 \ C) =
            planarFiber ((G₀.trans D) '' sphere (0 : E3) 1) t \ C := by
  classical
  obtain ⟨v, w, a₀, b₀, etaM, δM, Fm, Lm, Araw, Braw, hδM, hδMetaM,
      hetaMbound, _, hchain, hrect, hF, hFi, hheight, hdisjoint, hcentral,
      hends, hLm, hzero, hcuts⟩ :=
    exists_raw_recut_model_strips hh hunique hconnected d hd0 hdp hd hdi hform hr hrs
      (div_pos heta hscale)
  have hetaM : 0 < etaM := hδM.trans hδMetaM
  obtain ⟨hε, hphysicalzero, hphysical⟩ := physical_projected_recut_model_strips
    G₀ D h p d hscale hδM hGheight hDheight (fun i z => Fm i z) a₀ b₀ Araw Braw
    hzero (fun t ht i => ⟨((hcuts t ht).1 i).1, ((hcuts t ht).1 i).2.1⟩)
    (fun t ht => (hcuts t ht).2)
  let ε := scale * δM
  have hεeta : ε ≤ eta := by
    have hδbound : δM < eta / scale := hδMetaM.trans hetaMbound
    have hh := (lt_div_iff₀ hscale).mp hδbound
    dsimp [ε]
    linarith
  have htime {t : Real} (ht : t ∈ Icc (-ε) ε) : t ∈ Icc (-eta) eta :=
    ⟨by linarith [ht.1], ht.2.trans hεeta⟩
  have htimeOpen {t : Real} (ht : t ∈ Ioo (-ε) ε) : t ∈ Ioo (-eta) eta :=
    ⟨by linarith [ht.1], ht.2.trans_le hεeta⟩
  obtain ⟨hclosed, hopen⟩ := matching_square_images_of_positive_scale
    e d G₀ g hscale hmatch
  have hQUmodel : G₀ '' ((fun x => (d x : E3)) '' closedSquare r) ⊆ U :=
    hclosed.subset.trans hQU
  have hQU' : (fun q : S2 => G₀ q) '' (d '' closedSquare r) ⊆ U := by
    simpa only [image_image] using hQUmodel
  have hflatclosed : flattenedSphereMap G₀ D '' (d '' closedSquare r) =
      (D ∘ g) '' (e '' closedSquare (Real.sqrt scale * r)) := by
    have heq := congrArg (fun Z : Set E3 => D '' Z) hclosed
    simpa only [image_image, flattenedSphereMap, Function.comp_apply] using heq
  have hflatopen : flattenedSphereMap G₀ D '' (d '' openSquare r) =
      (D ∘ g) '' (e '' openSquare (Real.sqrt scale * r)) := by
    have heq := congrArg (fun Z : Set E3 => D '' Z) hopen
    simpa only [image_image, flattenedSphereMap, Function.comp_apply] using heq
  let j₀ : Fin 2 → Fin 2 := fun i => (La.symm (Lm (i, 0))).1
  let j₁ : Fin 2 → Fin 2 := fun i => (La.symm (Lm (i, 1))).1
  let q₀ : Fin 2 → Real := fun i => stripEndpoint aa₀ ab₀ (La.symm (Lm (i, 0)))
  let q₁ : Fin 2 → Real := fun i => stripEndpoint aa₀ ab₀ (La.symm (Lm (i, 1)))
  have hleft (i : Fin 2) : q₀ i ∈ Ioo (a (j₀ i)) (b (j₀ i)) ∧
      G₀ (Fm i (a₀ i, 0)) = g (Fa (j₀ i) (q₀ i, 0)) ∧
      G₀ (Fm i (a₀ i, 0)) ∈ U := by
    have hh := matching_contact_transfer e d G₀ g hr hmatch
      (fun i z => Fa i z) (fun i z => Fm i z) a b aa₀ ab₀ a₀ b₀ hachain La Lm
      hLa hLm hQUmodel (i, 0)
    simpa [j₀, q₀, stripEndpoint] using hh
  have hright (i : Fin 2) : q₁ i ∈ Ioo (a (j₁ i)) (b (j₁ i)) ∧
      G₀ (Fm i (b₀ i, 0)) = g (Fa (j₁ i) (q₁ i, 0)) ∧
      G₀ (Fm i (b₀ i, 0)) ∈ U := by
    have hh := matching_contact_transfer e d G₀ g hr hmatch
      (fun i z => Fa i z) (fun i z => Fm i z) a b aa₀ ab₀ a₀ b₀ hachain La Lm
      hLa hLm hQUmodel (i, 1)
    simpa [j₁, q₁, stripEndpoint] using hh
  have hGstrip (i : Fin 2) (z : Real × Real) (hz : z ∈ (Fm i).source) :
      G₀ (Fm i z) 2 = scale * z.2 := by
    rw [hGheight, hheight i z hz]
    ring
  let A : Fin 2 → Real → Real := fun i t => Araw i (t / scale)
  let B : Fin 2 → Real → Real := fun i t => Braw i (t / scale)
  have h0 : (0 : Real) ∈ Icc (-ε) ε := ⟨by linarith, hε.le⟩
  obtain ⟨δ, C, K, O, N, V, hδ, hδε, hC, hCNreg, hK, hO, hCO, hKO,
      hN, hCN, hNNreg, hV, hQV, hclosedC, hVC, hsource, hcommonN,
      Psi, hPsi0, hPsi, hPsiinv, hfix, hfixO, hmove⟩ :=
    exists_relative_model_slab_transport_of_raw_model_strips G₀ D hDheight hDzero h (h p) d
      hr hscale hrs hform Fm v a₀ b₀ w hchain
      (fun i z hz => hrect i ⟨hz.1, by
        have hz0 : z.2 = 0 := hz.2
        rw [hz0]
        exact ⟨by linarith, hetaM.le⟩⟩)
      hF hFi hheight hGstrip hdisjoint hcentral hends g hg hginj hU hcommon hQU'
      Fa a b hε (fun i z hz => hFa i ⟨hz.1, htimeOpen hz.2⟩)
      (fun i z hz => hactualheight i z ⟨hz.1, htimeOpen hz.2⟩)
      (fun i x hx t ht => hflat i x hx t (htimeOpen ht)) j₀ j₁ q₀ q₁
      (fun i => (hleft i).1) (fun i => (hright i).1)
      (fun i => (hleft i).2.1) (fun i => (hright i).2.1)
      (fun i => (hleft i).2.2) (fun i => (hright i).2.2)
      A B (fun i => ((hphysical 0 h0).1 i).1) (fun i => ((hphysical 0 h0).1 i).2)
      (fun i => (hphysicalzero i).1) (fun i => (hphysicalzero i).2)
      (fun t ht => (hphysical t ht).2) S
      (fun t ht => by rw [hflatopen]; exact hactual t (htime ht))
      Nreg hNreg (by rw [hflatclosed]; exact hQNreg)
  refine ⟨δ, C, K, O, N, V, hδ, hδε.trans hεeta, hC, hCNreg, hK, hO, hCO, hKO,
    hN, hCN, hNNreg, hV, ?_, ?_, hVC, hsource, hcommonN,
    Psi, hPsi0, hPsi, hPsiinv, hfix, hfixO, hmove⟩
  · exact hflatclosed ▸ hQV
  · exact hflatclosed ▸ hclosedC

theorem exists_concrete_nested_model_slab_transport
    (T D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ x : E3, D x 2 = x 2)
    (hDzero : ∀ x : E3, x 2 = 0 → D x = x)
    {p : S2} (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0)
    (hpz : (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8))
    (d : OpenPartialHomeomorph E2 S2) (hd0 : 0 ∈ d.source) (hdp : d 0 = p)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    (hform : ∀ x ∈ d.source, height (d x) = height p - x 0 ^ 2 + x 1 ^ 2)
    {r scale : Real} (hr : 0 < r) (hscale : 0 < scale)
    (hrs : closedSquare r ⊆ d.source)
    (hGheight : ∀ q : S2, nestedSlabMap T q 2 = scale * (height q - height p))
    (g : S2 → E3) (hg : Continuous g) (hginj : Injective g)
    (e : E2 → S2)
    (hmatch : ∀ x ∈ closedSquare r,
      nestedSlabMap T (d x) = g (e (Real.sqrt scale • x)))
    {U : Set E3} (hU : IsOpen U)
    (hcommon : (nestedSlabMap T '' sphere (0 : E3) 1) ∩ U = range g ∩ U)
    (hQU : g '' (e '' closedSquare (Real.sqrt scale * r)) ⊆ U)
    (Fa : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
    (a aa₀ ab₀ b : Fin 2 → Real)
    (hachain : ∀ i, a i < aa₀ i ∧ aa₀ i < ab₀ i ∧ ab₀ i < b i)
    (La : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2))
    (hLa : ∀ k, Fa k.1 (stripEndpoint aa₀ ab₀ k, 0) =
      e (contact (Real.sqrt scale * r) (La k)))
    {eta : Real} (heta : 0 < eta)
    (hFa : ∀ i, Ioo (a i) (b i) ×ˢ Ioo (-eta) eta ⊆ (Fa i).source)
    (hactualheight : ∀ i z, z ∈ Ioo (a i) (b i) ×ˢ Ioo (-eta) eta →
      g (Fa i z) 2 = z.2)
    (hflat : ∀ i x, x ∈ Icc (a i) (b i) → ∀ t ∈ Ioo (-eta) eta,
      D (g (Fa i (x, t))) =
        g (Fa i (x, 0)) + t • (EuclideanSpace.single 2 1 : E3))
    (S : Set E2)
    (hactual : ∀ t ∈ Icc (-eta) eta,
      range (D ∘ g) ∩ {y : E3 | y 2 = t} =
        (((D ∘ g) '' (e '' openSquare (Real.sqrt scale * r))) ∩
          {y : E3 | y 2 = t}) ∪ slice S t)
    (Nreg : Set E2) (hNreg : IsOpen Nreg)
    (hQNreg : toE2 '' (((D ∘ g) '' (e '' closedSquare (Real.sqrt scale * r))) ∩
      {y : E3 | y 2 = 0}) ⊆ Nreg) :
    ∃ (δ : Real) (C K O N : Set E2) (V : Set E3),
      0 < δ ∧ δ ≤ eta ∧ IsCompact C ∧ C ⊆ Nreg ∧ IsCompact K ∧ IsOpen O ∧
      C ⊆ O ∧ Disjoint K O ∧ IsOpen N ∧ C ⊆ N ∧ N ⊆ Nreg ∧ IsOpen V ∧
      (D ∘ g) '' (e '' closedSquare (Real.sqrt scale * r)) ⊆ V ∧
      (∀ t ∈ Icc (-δ) δ,
        planarFiber ((D ∘ g) '' (e '' closedSquare (Real.sqrt scale * r))) t ⊆ C) ∧
      (∀ t ∈ Icc (-δ) δ, ∀ x, toE3 x t ∈ V → x ∈ C) ∧
      (∀ t ∈ Icc (-δ) δ,
        planarFiber (range (D ∘ g)) t \ C = planarFiber (range (D ∘ g)) 0 \ C) ∧
      (∀ t ∈ Icc (-δ) δ,
        planarFiber (range (D ∘ g)) t ∩ N =
          planarFiber (((nestedSlabMap T).trans D) '' sphere (0 : E3) 1) t ∩ N) ∧
      ∃ Psi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Psi 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Psi z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Psi z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Psi t x = x) ∧
        (∀ t x, x ∈ O → Psi t x = x) ∧
        ∀ t ∈ Icc (-δ) δ,
          Psi t '' (planarFiber (((nestedSlabMap T).trans D) '' sphere (0 : E3) 1) 0 \ C) =
            planarFiber (((nestedSlabMap T).trans D) '' sphere (0 : E3) 1) t \ C := by
  obtain ⟨p₀, hp₀z, hp₀height, hp₀crit, _⟩ := exists_unique_critical_point_in_height_band
  have hpp₀ : p = p₀ := critical_latitude_unique_in_saddle_interval hp hp₀crit
    (Ioo_subset_Icc_self hpz) (Ioo_subset_Icc_self hp₀z)
  have hpheight : height p ∈ Ioo (1 : Real) (41 / 40) := hpp₀ ▸ hp₀height
  have hunique (q : S2) (hq : height q = height p)
      (hqcrit : mfderiv (𝓡 2) 𝓘(Real, Real) height q = 0) : q = p := by
    apply (critical_in_height_band_iff_eq_saddle hp hpz q ?_).mp hqcrit
    rw [hq]
    exact ⟨hpheight.1.le, by linarith [hpheight.2]⟩
  exact exists_model_slab_transport_of_central_level (nestedSlabMap T) D
    hDheight hDzero height_contMDiff hunique
    (isConnected_critical_level_of_saddle_latitude hp hpz).isPreconnected
    d hd0 hdp hd hdi hform hr hscale hrs hGheight g hg hginj e hmatch
    hU hcommon hQU Fa a aa₀ ab₀ b hachain La hLa heta hFa hactualheight hflat
    S hactual Nreg hNreg hQNreg

private theorem exists_concrete_nested_slab_matching
    (T D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ x : E3, D x 2 = x 2)
    (hDzero : ∀ x : E3, x 2 = 0 → D x = x)
    {p : S2} (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0)
    (hpz : (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8))
    (d : OpenPartialHomeomorph E2 S2) (hd0 : 0 ∈ d.source) (hdp : d 0 = p)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    (hform : ∀ x ∈ d.source, height (d x) = height p - x 0 ^ 2 + x 1 ^ 2)
    {r scale : Real} (hr : 0 < r) (hscale : 0 < scale)
    (hrs : closedSquare r ⊆ d.source)
    (hGheight : ∀ q : S2, nestedSlabMap T q 2 = scale * (height q - height p))
    (g : S2 → E3) (hg : Continuous g) (hginj : Injective g)
    (e : E2 → S2)
    (hmatch : ∀ x ∈ closedSquare r,
      nestedSlabMap T (d x) = g (e (Real.sqrt scale • x)))
    {U : Set E3} (hU : IsOpen U)
    (hcommon : (nestedSlabMap T '' sphere (0 : E3) 1) ∩ U = range g ∩ U)
    (hQU : g '' (e '' closedSquare (Real.sqrt scale * r)) ⊆ U)
    (Fa : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
    (a aa₀ ab₀ b : Fin 2 → Real)
    (hachain : ∀ i, a i < aa₀ i ∧ aa₀ i < ab₀ i ∧ ab₀ i < b i)
    (La : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2))
    (hLa : ∀ k, Fa k.1 (stripEndpoint aa₀ ab₀ k, 0) =
      e (contact (Real.sqrt scale * r) (La k)))
    {eta : Real} (heta : 0 < eta)
    (hFa : ∀ i, Ioo (a i) (b i) ×ˢ Ioo (-eta) eta ⊆ (Fa i).source)
    (hactualheight : ∀ i z, z ∈ Ioo (a i) (b i) ×ˢ Ioo (-eta) eta →
      g (Fa i z) 2 = z.2)
    (hflat : ∀ i x, x ∈ Icc (a i) (b i) → ∀ t ∈ Ioo (-eta) eta,
      D (g (Fa i (x, t))) =
        g (Fa i (x, 0)) + t • (EuclideanSpace.single 2 1 : E3))
    (S : Set E2)
    (hactual : ∀ t ∈ Icc (-eta) eta,
      range (D ∘ g) ∩ {y : E3 | y 2 = t} =
        (((D ∘ g) '' (e '' openSquare (Real.sqrt scale * r))) ∩
          {y : E3 | y 2 = t}) ∪ slice S t)
    (Nreg : Set E2) (hNreg : IsOpen Nreg)
    (hQNreg : toE2 '' (((D ∘ g) '' (e '' closedSquare (Real.sqrt scale * r))) ∩
      {y : E3 | y 2 = 0}) ⊆ Nreg)
    (hregular : ∀ (C N : Set E2), IsCompact C → IsOpen N → C ⊆ N → N ⊆ Nreg →
      ∀ ε : Real, 0 < ε → ε ≤ eta →
      (∀ t ∈ Icc (-ε) ε,
        planarFiber (range (D ∘ g)) t ∩ N =
          planarFiber (((nestedSlabMap T).trans D) '' sphere (0 : E3) 1) t ∩ N) →
      ∀ t ∈ Icc (-ε) ε, t < 0 →
        ∃ K : Set E2, IsCompact K ∧ Disjoint K C ∧
          ∃ Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
            (∀ x, x ∉ K → Q x = x) ∧
            Q '' planarFiber (range (D ∘ g)) t =
              planarFiber (((nestedSlabMap T).trans D) '' sphere (0 : E3) 1) t) :
    ∃ (δ : Real) (C K O : Set E2) (V : Set E3),
      0 < δ ∧ δ ≤ eta ∧ IsCompact C ∧ C ⊆ Nreg ∧ IsCompact K ∧ IsOpen O ∧
      C ⊆ O ∧ Disjoint K O ∧ IsOpen V ∧
      (D ∘ g) '' (e '' closedSquare (Real.sqrt scale * r)) ⊆ V ∧
      (∀ t ∈ Icc (-δ) δ,
        planarFiber ((D ∘ g) '' (e '' closedSquare (Real.sqrt scale * r))) t ⊆ C) ∧
      ∃ Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Phi z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Phi t x = x) ∧
        (∀ t x, x ∈ O → Phi t x = x) ∧
        (∀ t ∈ Icc (-δ) δ, ∀ x, toE3 x t ∈ V → Phi t x = x) ∧
        ∀ t ∈ Icc (-δ) δ,
          Phi t '' planarFiber (range (D ∘ g)) t =
            planarFiber (((nestedSlabMap T).trans D) '' sphere (0 : E3) 1) t ∧
          ∀ P ⊆ C, Phi t '' (planarFiber (range (D ∘ g)) t \ P) =
            planarFiber (((nestedSlabMap T).trans D) '' sphere (0 : E3) 1) t \ P := by
  obtain ⟨δ, C, K, O, N, V, hδ, hδη, hC, hCNreg, hK, hO, hCO, hKO,
      hN, hCN, hNNreg, hV, hQV, hclosedC, hVC, hsource, hcommonN,
      Psi, hPsi0, hPsi, hPsiinv, hPsifix, hPsiO, hmove⟩ :=
    exists_concrete_nested_model_slab_transport T D hDheight hDzero hp hpz
      d hd0 hdp hd hdi hform hr hscale hrs hGheight g hg hginj e hmatch
      hU hcommon hQU Fa a aa₀ ab₀ b hachain La hLa heta hFa hactualheight hflat
      S hactual Nreg hNreg hQNreg
  have hcommonC (t : Real) (ht : t ∈ Icc (-δ) δ) :
      planarFiber (range (D ∘ g)) t ∩ C =
        planarFiber (((nestedSlabMap T).trans D) '' sphere (0 : E3) 1) t ∩ C := by
    have heq := congrArg (fun Z : Set E2 => Z ∩ C) (hcommonN t ht)
    simpa only [inter_assoc, inter_eq_self_of_subset_right hCN] using heq
  obtain ⟨K', O', hK', hO', hCO', hKO', Phi, hPhi, hPhiinv, hfix, hfixO, hmatch⟩ :=
    exists_relative_matching_of_model_transport hδ C K O hK hCO hKO
      (planarFiber (range (D ∘ g)))
      (planarFiber (((nestedSlabMap T).trans D) '' sphere (0 : E3) 1))
      hsource hcommonC Psi hPsi hPsifix hmove
      (hregular C N hC hN hCN hNNreg δ hδ hδη hcommonN)
  exact ⟨δ, C, K', O', V, hδ, hδη, hC, hCNreg, hK', hO', hCO', hKO',
    hV, hQV, hclosedC, Phi, hPhi, hPhiinv, hfix, hfixO,
    fun t ht x hx => hfixO t x (hCO' (hVC t ht x hx)), hmatch⟩

private theorem exists_nested_slab_family_of_negative_regular_matching
    (g : S2 → E3) (hg : Continuous g) (hginj : Injective g)
    (e d : OpenPartialHomeomorph E2 S2) (p : S2)
    (hp : 1 < height p) (hd0 : 0 ∈ d.source) (hdp : d 0 = p)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    (T D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    {scale ρ r eta : Real} (hscale : 0 < scale) (hρ : 0 < ρ)
    (hr : 0 < r) (hrρ : 2 * r < ρ) (heta : 0 < eta)
    (hsource : closedBall (0 : E2) ρ ⊆ d.source)
    (he : ∀ x ∈ closedBall (0 : E2) ρ, Real.sqrt scale • x ∈ e.source)
    (hactualform : ∀ x ∈ e.source, g (e x) 2 = -(x 0)^2 + (x 1)^2)
    (hmodelheight : ∀ q : S2, T (shear (3 / 10) q) 2 =
      scale * (height q - height p))
    (hmatch : ∀ x ∈ closedBall (0 : E2) ρ,
      T (shear (3 / 10) (d x)) = g (e (Real.sqrt scale • x)))
    (hDheight : ∀ x : E3, D x 2 = x 2)
    (hDzero : ∀ x : E3, x 2 = 0 → D x = x)
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
    (a a₀ b₀ b : Fin 2 → Real)
    (hchain : ∀ i, a i < a₀ i ∧ a₀ i < b₀ i ∧ b₀ i < b i)
    (L : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2))
    (hL : ∀ k, F k.1 (stripEndpoint a₀ b₀ k, 0) =
      e (contact (Real.sqrt scale * r) (L k)))
    (hFsource : ∀ i, Icc (a i) (b i) ×ˢ Icc (-eta) eta ⊆ (F i).source)
    (hFheight : ∀ i z, z ∈ (F i).source → g (F i z) 2 = z.2)
    (hflat : ∀ i t, t ∈ Icc (-eta) eta → ∀ s ∈ Icc (a i) (b i),
      D (g (F i (s, t))) =
        g (F i (s, 0)) + t • (EuclideanSpace.single 2 1 : E3))
    (A B : Fin 2 → Real → Real)
    (hcuts : ∀ i t, t ∈ Icc (-eta) eta → a i ≤ A i t ∧ B i t ≤ b i)
    (hexterior : ∀ t ∈ Icc (-eta) eta,
      (D ∘ g) '' ({q : S2 | g q 2 = t} \ e '' openSquare (Real.sqrt scale * r)) =
        ⋃ i, (fun s => g (F i (s, 0)) + t • (EuclideanSpace.single 2 1 : E3)) ''
          Icc (A i t) (B i t))
    (Nreg : Set E2) (hNreg : IsOpen Nreg)
    (hQNreg : toE2 '' (((D ∘ g) '' (e '' closedSquare (Real.sqrt scale * r))) ∩
      {y : E3 | y 2 = 0}) ⊆ Nreg)
    (hregular : ∀ C N : Set E2, IsCompact C → IsOpen N → C ⊆ N → N ⊆ Nreg →
      ∀ ε : Real, 0 < ε → ε ≤ eta →
      (∀ t ∈ Icc (-ε) ε,
        {x : E2 | toE3 x t ∈ range (D ∘ g)} ∩ N =
          {x : E2 | polynomial (3 / 10) (T.symm (D.symm (toE3 x t))) = 1} ∩ N) →
      ∀ t ∈ Icc (-ε) ε, t < 0 →
        ∃ K : Set E2, IsCompact K ∧ Disjoint K C ∧
          ∃ Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
            (∀ x, x ∉ K → Q x = x) ∧
            Q '' {x : E2 | toE3 x t ∈ range (D ∘ g)} =
              {x : E2 | polynomial (3 / 10) (T.symm (D.symm (toE3 x t))) = 1}) :
    ∃ (δ : Real) (K : Set E2) (V : Set E3),
      0 < δ ∧ δ ≤ eta ∧ IsCompact K ∧ IsOpen V ∧
      (D ∘ g) '' (e '' closedSquare (Real.sqrt scale * r)) ⊆ V ∧
      ∃ Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Phi z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Phi t x = x) ∧
        (∀ t ∈ Icc (-δ) δ, ∀ x, toE3 x t ∈ V → Phi t x = x) ∧
        ∀ t ∈ Icc (-δ) δ,
          Phi t '' {x : E2 | toE3 x t ∈ range (D ∘ g)} =
            {x : E2 | polynomial (3 / 10) (T.symm (D.symm (toE3 x t))) = 1} ∧
          Phi t '' (⋃ i, (fun s => toE2 (g (F i (s, 0)))) '' Icc (A i t) (B i t)) =
            {x : E2 | polynomial (3 / 10) (T.symm (D.symm (toE3 x t))) = 1} \
              {x : E2 | toE3 x t ∈ (D ∘ g) '' (e '' openSquare (Real.sqrt scale * r))} := by
  classical
  obtain ⟨hcritical, hlatitude, d', hd'0, hd'p, hd', hdi', hd'source, hd'form,
      hd'eq, U, hU, hQU, hcommon⟩ :=
    exists_nested_chart_and_common_neighborhood g hg hginj e d p hp hd0 hdp hd hdi
      T hscale hρ hr hrρ hsource he hactualform hmodelheight hmatch
  have hmatch' (x : E2) (hx : x ∈ closedSquare r) :
      nestedSlabMap T (d' x) = g (e (Real.sqrt scale • x)) := by
    rw [hd'eq]
    exact hmatch x ((closedBall_subset_closedBall hrρ.le)
      (closedSquare_subset_closedBall hr.le hx))
  have hQUactual : g '' (e '' closedSquare (Real.sqrt scale * r)) ⊆ U := by
    have hclosed := (matching_square_images_of_positive_scale
      e d' (nestedSlabMap T) g hscale hmatch').1
    have hmodelQ : nestedSlabMap T '' ((fun x => (d' x : E3)) '' closedSquare r) ⊆ U := by
      rw [image_image]
      change (fun x => T (shear (3 / 10) (d' x))) '' closedSquare r ⊆ U
      simpa only [image_image] using hQU
    exact hclosed ▸ hmodelQ
  have hzero (i : Fin 2) (s : Real) (hs : s ∈ Icc (a i) (b i)) :
      g (F i (s, 0)) 2 = 0 :=
    hFheight i (s, 0) (hFsource i ⟨hs, ⟨by linarith, heta.le⟩⟩)
  have hactual := actual_moving_cuts_and_whole_level_of_flattening
    g hginj D hDheight e (Real.sqrt scale * r) (fun i z => F i z)
    a b A B hzero hflat hcuts hexterior
  have hsphere : ((nestedSlabMap T).trans D) '' sphere (0 : E3) 1 =
      {y : E3 | polynomial (3 / 10) (T.symm (D.symm y)) = 1} := by
    calc
      _ = D '' (T '' (shear (3 / 10) '' sphere (0 : E3) 1)) := by
        rw [image_image, image_image]
        rfl
      _ = _ := flattened_sphere_eq T D
  have hmodel (t : Real) :
      planarFiber (((nestedSlabMap T).trans D) '' sphere (0 : E3) 1) t =
        {x : E2 | polynomial (3 / 10) (T.symm (D.symm (toE3 x t))) = 1} := by
    rw [planarFiber, hsphere]
    rfl
  obtain ⟨δ, C, K, O, V, hδ, hδη, hC, _, hK, _, _, _, hV, hQV, hprotected,
      Phi, hPhi, hPhiinv, hfix, _, hfixV, hmatching⟩ :=
    exists_concrete_nested_slab_matching T D hDheight hDzero hcritical hlatitude
      d' hd'0 hd'p hd' hdi' hd'form hr hscale hd'source hmodelheight
      g hg hginj e hmatch' hU hcommon hQUactual F a a₀ b₀ b hchain L hL heta
      (fun i z hz => hFsource i ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩)
      (fun i z hz => hFheight i z
        (hFsource i ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩))
      (fun i s hs t ht => hflat i t (Ioo_subset_Icc_self ht) s hs)
      (⋃ i, (fun s => toE2 (g (F i (s, 0)))) '' Icc (a i) (b i))
      (fun t ht => (hactual t ht).2) Nreg hNreg hQNreg
      (by
        intro C N hC hN hCN hNNreg ε hε hεη hcommon t ht ht0
        have hc : ∀ u ∈ Icc (-ε) ε,
            {x : E2 | toE3 x u ∈ range (D ∘ g)} ∩ N =
              {x : E2 | polynomial (3 / 10) (T.symm (D.symm (toE3 x u))) = 1} ∩ N := by
          intro u hu
          rw [← hmodel u]
          exact hcommon u hu
        obtain ⟨J, hJ, hJC, Q, hQfix, hQ⟩ := hregular C N hC hN hCN hNNreg ε hε hεη hc t ht ht0
        exact ⟨J, hJ, hJC, Q, hQfix, (by rw [hmodel]; exact hQ)⟩)
  refine ⟨δ, K, V, hδ, hδη, hK, hV, hQV, Phi, hPhi, hPhiinv, hfix, hfixV, ?_⟩
  intro t ht
  have htη : t ∈ Icc (-eta) eta := ⟨by linarith [ht.1], ht.2.trans hδη⟩
  have hPC : {x : E2 | toE3 x t ∈
      (D ∘ g) '' (e '' openSquare (Real.sqrt scale * r))} ⊆ C := by
    intro x hx
    apply hprotected t ht
    exact (image_mono (image_mono (openSquare_subset_closedSquare _))) hx
  refine ⟨(hmatching t ht).1.trans (hmodel t), ?_⟩
  rw [← (hactual t htη).1, ← hmodel t]
  exact (hmatching t ht).2 _ hPC

theorem exists_nested_slab_family
    (g : S2 → E3) (hg : Continuous g) (hginj : Injective g)
    (e d : OpenPartialHomeomorph E2 S2) (p : S2)
    (hp : 1 < height p) (hd0 : 0 ∈ d.source) (hdp : d 0 = p)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    (T D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    {scale ρ r eta : Real} (hscale : 0 < scale) (hρ : 0 < ρ)
    (hr : 0 < r) (hrρ : 2 * r < ρ) (heta : 0 < eta)
    (hsource : closedBall (0 : E2) ρ ⊆ d.source)
    (he : ∀ x ∈ closedBall (0 : E2) ρ, Real.sqrt scale • x ∈ e.source)
    (hactualform : ∀ x ∈ e.source, g (e x) 2 = -(x 0)^2 + (x 1)^2)
    (hmodelheight : ∀ q : S2, T (shear (3 / 10) q) 2 =
      scale * (height q - height p))
    (hmatch : ∀ x ∈ closedBall (0 : E2) ρ,
      T (shear (3 / 10) (d x)) = g (e (Real.sqrt scale • x)))
    (hDheight : ∀ x : E3, D x 2 = x 2)
    (hDzero : ∀ x : E3, x 2 = 0 → D x = x)
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
    (a a₀ b₀ b : Fin 2 → Real)
    (hchain : ∀ i, a i < a₀ i ∧ a₀ i < b₀ i ∧ b₀ i < b i)
    (L : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2))
    (hL : ∀ k, F k.1 (stripEndpoint a₀ b₀ k, 0) =
      e (contact (Real.sqrt scale * r) (L k)))
    (hFsource : ∀ i, Icc (a i) (b i) ×ˢ Icc (-eta) eta ⊆ (F i).source)
    (hFheight : ∀ i z, z ∈ (F i).source → g (F i z) 2 = z.2)
    (hflat : ∀ i t, t ∈ Icc (-eta) eta → ∀ s ∈ Icc (a i) (b i),
      D (g (F i (s, t))) =
        g (F i (s, 0)) + t • (EuclideanSpace.single 2 1 : E3))
    (A B : Fin 2 → Real → Real)
    (hcuts : ∀ i t, t ∈ Icc (-eta) eta → a i ≤ A i t ∧ B i t ≤ b i)
    (hexterior : ∀ t ∈ Icc (-eta) eta,
      (D ∘ g) '' ({q : S2 | g q 2 = t} \ e '' openSquare (Real.sqrt scale * r)) =
        ⋃ i, (fun s => g (F i (s, 0)) + t • (EuclideanSpace.single 2 1 : E3)) ''
          Icc (A i t) (B i t))
    (Nreg : Set E2) (hNreg : IsOpen Nreg)
    (hQNreg : toE2 '' (((D ∘ g) '' (e '' closedSquare (Real.sqrt scale * r))) ∩
      {y : E3 | y 2 = 0}) ⊆ Nreg)
    (hregular : ∀ C N : Set E2, IsCompact C → IsOpen N → C ⊆ N → N ⊆ Nreg →
      ∀ ε : Real, 0 < ε → ε ≤ eta →
      (∀ t ∈ Icc (-ε) ε,
        {x : E2 | toE3 x t ∈ range (D ∘ g)} ∩ N =
          {x : E2 | polynomial (3 / 10) (T.symm (D.symm (toE3 x t))) = 1} ∩ N) →
      ∀ t ∈ Icc (-ε) ε, t ≠ 0 →
        ∃ K : Set E2, IsCompact K ∧ Disjoint K C ∧
          ∃ Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
            (∀ x, x ∉ K → Q x = x) ∧
            Q '' {x : E2 | toE3 x t ∈ range (D ∘ g)} =
              {x : E2 | polynomial (3 / 10) (T.symm (D.symm (toE3 x t))) = 1}) :
    ∃ (δ : Real) (K : Set E2) (V : Set E3),
      0 < δ ∧ δ ≤ eta ∧ IsCompact K ∧ IsOpen V ∧
      (D ∘ g) '' (e '' closedSquare (Real.sqrt scale * r)) ⊆ V ∧
      ∃ Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Phi z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Phi t x = x) ∧
        (∀ t ∈ Icc (-δ) δ, ∀ x, toE3 x t ∈ V → Phi t x = x) ∧
        ∀ t ∈ Icc (-δ) δ,
          Phi t '' {x : E2 | toE3 x t ∈ range (D ∘ g)} =
            {x : E2 | polynomial (3 / 10) (T.symm (D.symm (toE3 x t))) = 1} ∧
          Phi t '' (⋃ i, (fun s => toE2 (g (F i (s, 0)))) '' Icc (A i t) (B i t)) =
            {x : E2 | polynomial (3 / 10) (T.symm (D.symm (toE3 x t))) = 1} \
              {x : E2 | toE3 x t ∈ (D ∘ g) '' (e '' openSquare (Real.sqrt scale * r))} := by
  apply exists_nested_slab_family_of_negative_regular_matching
    g hg hginj e d p hp hd0 hdp hd hdi T D hscale hρ hr hrρ heta hsource he
    hactualform hmodelheight hmatch hDheight hDzero F a a₀ b₀ b hchain L hL
    hFsource hFheight hflat A B hcuts hexterior Nreg hNreg hQNreg
  intro C N hC hN hCN hNNreg ε hε hεeta hcommon t ht ht0
  exact hregular C N hC hN hCN hNNreg ε hε hεeta hcommon t ht (ne_of_lt ht0)

end SlabMatching

section RegularCircles

set_option backward.isDefEq.respectTransparency false

open TopologicalSpace Poincare.Geometry.Manifold.RegularLevel

private abbrev S1 := sphere (0 : E2) 1
private abbrev axis : E3 := EuclideanSpace.single 2 1
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩

private theorem isConnected_bottom_of_regular_band
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {a b : Real} (hab : a ≤ b)
    (hregular : ∀ q : S2, h q ∈ Icc a b → mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0)
    (htop : IsConnected (h ⁻¹' {b})) : IsConnected (h ⁻¹' {a}) := by
  obtain ⟨U, _, _, _, hfull, hreg, V, δ, Φ, _, _, _, _, _, _, _, hlevels⟩ :=
    exists_sphere_height_level_diffeomorphisms_on_regular_band_of_smooth hh hab hregular
  let := openLevelSetChartedSpace hh U hreg 1 a
  let := openLevelSetChartedSpace hh U hreg 1 b
  obtain ⟨e, _⟩ := hlevels b ⟨hab, le_rfl⟩
  let : ConnectedSpace ↥(h ⁻¹' {b}) := isConnected_iff_connectedSpace.mp htop
  let j : ↥(h ⁻¹' {b}) → openLevelSet h U b :=
    fun q => ⟨⟨q, (inter_eq_right.mp (hfull b ⟨hab, le_rfl⟩)) q.property⟩, q.property⟩
  have hj : Continuous j := (continuous_subtype_val.subtype_mk _).subtype_mk _
  let k : ↥(h ⁻¹' {b}) → S2 := openLevelIncl h U a ∘ e.symm ∘ j
  have hk : Continuous k :=
    (isEmbedding_openLevelIncl h U a).continuous.comp (e.symm.continuous.comp hj)
  have hrange : range k = h ⁻¹' {a} := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact (e.symm (j x)).property
    · intro hq
      let qa : openLevelSet h U a :=
        ⟨⟨q, (inter_eq_right.mp (hfull a ⟨le_rfl, hab⟩)) hq⟩, hq⟩
      let qb : ↥(h ⁻¹' {b}) := ⟨openLevelIncl h U b (e qa), (e qa).property⟩
      refine ⟨qb, ?_⟩
      change openLevelIncl h U a (e.symm (j qb)) = q
      have hjqb : j qb = e qa := rfl
      rw [hjqb, e.symm_apply_apply]
      rfl
  rw [← hrange]
  exact isConnected_range hk

private theorem exists_smooth_circle_above_nested_saddle
    {p : S2} (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0)
    (hpz : (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8))
    {a : Real} (hpa : height p < a) (ha : a ≤ (13 / 10 : Real)) :
    ∃ γ : S1 → S2,
      ContMDiff (𝓡 1) (𝓡 2) ∞ γ ∧ Injective γ ∧
      (∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) γ q)) ∧
      range γ = height ⁻¹' {a} := by
  obtain ⟨p₀, hp₀z, hp₀h, hp₀, _⟩ := exists_unique_critical_point_in_height_band
  have hp₀p : p₀ = p := critical_latitude_unique_in_saddle_interval hp₀ hp
    (Ioo_subset_Icc_self hp₀z) (Ioo_subset_Icc_self hpz)
  have hph : (1 : Real) < height p := hp₀p ▸ hp₀h.1
  have hregular (q : S2) (hq : height q ∈ Icc a (13 / 10 : Real)) :
      mfderiv (𝓡 2) 𝓘(Real, Real) height q ≠ 0 := by
    intro hqcrit
    have hqp := (critical_in_height_band_iff_eq_saddle hp hpz q
      ⟨hph.le.trans (hpa.le.trans hq.1), hq.2⟩).mp hqcrit
    subst q
    exact hpa.not_ge hq.1
  have hconn := isConnected_bottom_of_regular_band height_contMDiff ha hregular
    isConnected_upper_height_level
  obtain ⟨q, hq⟩ := hconn.nonempty
  obtain ⟨γ, hγ, hinj, hder, hrange⟩ := exists_smooth_circle_regularLevelComponent
    height_contMDiff a (fun q hq => hregular q ⟨hq.ge, hq.trans_le ha⟩) q hq
  refine ⟨γ, hγ, hinj, hder, ?_⟩
  rw [hrange, hconn.isPreconnected.connectedComponentIn hq]

private theorem planar_circle_of_spherical_level
    (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (γ : S1 → S2) (hγ : ContMDiff (𝓡 1) (𝓡 2) ∞ γ)
    (hinj : Injective γ) (hder : ∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) γ q))
    {t : Real} (hrange : range γ = {p : S2 | G p 2 = t}) :
    let β : S1 → E2 := fun q => toE2 (G (γ q))
    ContMDiff (𝓡 1) (𝓡 2) ∞ β ∧ Injective β ∧
      (∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) β q)) ∧
      range β = {x : E2 | toE3 x t ∈ G '' sphere (0 : E3) 1} := by
  let g : S2 → E3 := fun p => G p
  have hg : ContMDiff (𝓡 2) (𝓡 3) ∞ g :=
    G.contMDiff.comp (contMDiff_coe_sphere (n := 2) (m := ∞) (E := E3))
  have hgd (p : S2) : Injective (mfderiv (𝓡 2) (𝓡 3) g p) := by
    rw [show g = G ∘ (Subtype.val : S2 → E3) from rfl,
      mfderiv_comp p (G.contMDiff.mdifferentiable (by simp) (p : E3))
        ((contMDiff_coe_sphere (n := 2) (m := ∞) (E := E3) p).mdifferentiableAt (by simp))]
    apply (G.mfderivToContinuousLinearEquiv (by simp) (p : E3)).injective.comp
    convert! injective_mvfderiv_subtypeVal_sphere p
  let β : S1 → E2 := fun q => toE2 (G (γ q))
  have hβ : ContMDiff (𝓡 1) (𝓡 2) ∞ β := contDiff_toE2.contMDiff.comp (hg.comp hγ)
  have hheight (q : S1) : G (γ q) 2 = t := by
    have : γ q ∈ range γ := mem_range_self q
    rw [hrange] at this
    exact this
  have hfull : g ∘ γ = (fun x => toE3 x t) ∘ β := by
    funext q
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact hheight q
  refine ⟨hβ, ?_, ?_, ?_⟩
  · intro q z hqz
    apply hinj
    apply Subtype.ext
    apply G.injective
    calc
      G (γ q) = toE3 (β q) t := congrFun hfull q
      _ = toE3 (β z) t := congrArg (fun x => toE3 x t) hqz
      _ = G (γ z) := (congrFun hfull z).symm
  · intro q
    have hfullinj : Injective (mfderiv (𝓡 1) (𝓡 3) (g ∘ γ) q) := by
      rw [mfderiv_comp q (hg.mdifferentiable (by simp) (γ q))
        (hγ.mdifferentiable (by simp) q)]
      exact (hgd (γ q)).comp (hder q)
    rw [hfull, mfderiv_comp q
      ((contDiff_toE3 t).contMDiff.mdifferentiable (by simp) (β q))
      (hβ.mdifferentiable (by simp) q)] at hfullinj
    intro v w hvw
    apply hfullinj
    exact congrArg (mfderiv (𝓡 2) (𝓡 3) (fun x => toE3 x t) (β q)) hvw
  · ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨γ q, (γ q).property, congrFun hfull q⟩
    · rintro ⟨y, hy, hxy⟩
      have hyt : G (⟨y, hy⟩ : S2) 2 = t := by
        rw [hxy]
        rfl
      have hyrange : (⟨y, hy⟩ : S2) ∈ range γ := by rw [hrange]; exact hyt
      obtain ⟨q, hq⟩ := hyrange
      refine ⟨q, ?_⟩
      dsimp [β]
      rw [hq]
      have heq := congrArg toE2 hxy
      exact heq.trans (by ext i; fin_cases i <;> rfl)

private theorem exists_smooth_planar_circle_positive_nested_level
    (T D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ x : E3, D x 2 = x 2)
    {p : S2} (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0)
    (hpz : (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8))
    {scale t : Real} (hscale : 0 < scale) (ht : 0 < t)
    (htupper : height p + t / scale ≤ (13 / 10 : Real))
    (hGheight : ∀ q : S2,
      ((shear (3 / 10)).trans T) q 2 = scale * (height q - height p)) :
    ∃ β : S1 → E2,
      ContMDiff (𝓡 1) (𝓡 2) ∞ β ∧ Injective β ∧
      (∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) β q)) ∧
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ β ∧
      range β = {x : E2 | toE3 x t ∈
        (((shear (3 / 10)).trans T).trans D) '' sphere (0 : E3) 1} := by
  let G := ((shear (3 / 10)).trans T).trans D
  obtain ⟨γ, hγ, hγinj, hγder, hγrange⟩ := exists_smooth_circle_above_nested_saddle
    hp hpz (lt_add_of_pos_right _ (div_pos ht hscale)) htupper
  have hlevel : height ⁻¹' {height p + t / scale} = {q : S2 | G q 2 = t} := by
    ext q
    change height q = height p + t / scale ↔ D (((shear (3 / 10)).trans T) q) 2 = t
    rw [hDheight, hGheight]
    have hcancel : scale * (t / scale) = t := by field_simp
    constructor <;> intro hh <;> nlinarith [hcancel]
  obtain ⟨hβ, hβinj, hβder, hβrange⟩ := planar_circle_of_spherical_level G γ hγ hγinj
    hγder (hγrange.trans hlevel)
  exact ⟨_, hβ, hβinj, hβder,
    Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv hβ hβinj hβder,
    hβrange⟩

theorem exists_uniform_positive_nested_level_circles
    (T D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ x : E3, D x 2 = x 2)
    {p : S2} (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0)
    (hpz : (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8))
    {scale : Real} (hscale : 0 < scale)
    (hGheight : ∀ q : S2,
      ((shear (3 / 10)).trans T) q 2 = scale * (height q - height p)) :
    ∃ ε : Real, 0 < ε ∧ ∀ t ∈ Ioc (0 : Real) ε,
      ∃ β : S1 → E2,
        ContMDiff (𝓡 1) (𝓡 2) ∞ β ∧ Injective β ∧
        (∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) β q)) ∧
        _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ β ∧
        ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞
          (fun z : Real × S1 => β z.2) ∧
        range β = {x : E2 | toE3 x t ∈
          (((shear (3 / 10)).trans T).trans D) '' sphere (0 : E3) 1} := by
  have hheight : height p < (13 / 10 : Real) :=
    (saddle_height_lt_fortyone_fortieths hp hpz).trans (by norm_num)
  refine ⟨scale * (13 / 10 - height p), mul_pos hscale (sub_pos.mpr hheight), ?_⟩
  intro t ht
  have htupper : height p + t / scale ≤ (13 / 10 : Real) := by
    have := (div_le_iff₀ hscale).mpr (show t ≤ (13 / 10 - height p) * scale by
      simpa only [mul_comm] using ht.2)
    linarith
  obtain ⟨β, hβ, hβinj, hβder, hβemb, hβrange⟩ :=
    exists_smooth_planar_circle_positive_nested_level T D hDheight hp hpz
      hscale ht.1 htupper hGheight
  exact ⟨β, hβ, hβinj, hβder, hβemb, hβ.comp contMDiff_snd, hβrange⟩

private theorem toE3_toE2_of_height {y : E3} {t : Real} (hy : y 2 = t) :
    toE3 (toE2 y) t = y := by
  ext i
  fin_cases i <;> simp [toE3, toE2, hy]

private theorem toE2_toE3' (x : E2) (t : Real) : toE2 (toE3 x t) = x := by
  ext i
  fin_cases i <;> rfl

private theorem smooth_projection_circle {f : S1 → E3}
    (hf : ContMDiff (𝓡 1) (𝓡 3) ∞ f) (hinj : Injective f)
    (hder : ∀ q, Injective (mfderiv (𝓡 1) (𝓡 3) f q))
    {t : Real} (hh : ∀ q, f q 2 = t) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (toE2 ∘ f) := by
  have hp : ContDiff Real ∞ toE2 := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · change ContDiff Real ∞ (fun x : E3 => x 0)
      fun_prop
    · change ContDiff Real ∞ (fun x : E3 => x 1)
      fun_prop
  have hl : ContDiff Real ∞ (fun x : E2 => toE3 x t) := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · change ContDiff Real ∞ (fun x : E2 => x 0)
      fun_prop
    · change ContDiff Real ∞ (fun x : E2 => x 1)
      fun_prop
    · exact contDiff_const
  have hc := hp.contMDiff.comp hf
  have heq : (fun x : E2 => toE3 x t) ∘ (toE2 ∘ f) = f :=
    funext (fun q => toE3_toE2_of_height (hh q))
  apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv hc
  · intro p q hpq
    apply hinj
    calc
      f p = toE3 (toE2 (f p)) t := (toE3_toE2_of_height (hh p)).symm
      _ = toE3 (toE2 (f q)) t := congrArg (fun x => toE3 x t) hpq
      _ = f q := toE3_toE2_of_height (hh q)
  · intro p u v huv
    apply hder p
    have hd := mfderiv_comp p (hl.contMDiff.mdifferentiable (by simp) _)
      (hc.mdifferentiable (by simp) p)
    rw [heq] at hd
    rw [hd]
    change (mfderiv (𝓡 2) (𝓡 3) (fun x : E2 => toE3 x t) _)
      ((mfderiv (𝓡 1) (𝓡 2) (toE2 ∘ f) p) u) = _
    rw [huv]
    rfl

open SphereSurgeryCoreCap

private def upperPlanarCutCircle {g : S2 → E3} {B : Set Real} {K : Set S2}
    (A : AnnularEndFamily axis g B K)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (i : A.UpperCutIndex) (q : S1) : E2 :=
  toE2 (D (g (A.upperCutCircle i q)))

private theorem upperPlanarCutCircle_geometry {g : S2 → E3} {B : Set Real} {K : Set S2}
    (A : AnnularEndFamily axis g B K)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hD : ∀ y, D y 2 = y 2) :
    (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞
      (upperPlanarCutCircle A D i)) ∧
    Injective (fun z : A.UpperCutIndex × S1 => upperPlanarCutCircle A D z.1 z.2) ∧
    (⋃ i, range (upperPlanarCutCircle A D i)) =
      {x : E2 | toE3 x A.upperCut ∈ range (D ∘ g)} := by
  have hheight (i : A.UpperCutIndex) (q : S1) :
      g (A.upperCutCircle i q) 2 = A.upperCut := by
    simpa [axis, PiLp.inner_apply] using A.upperCutCircle_height i q
  have hheightD (i : A.UpperCutIndex) (q : S1) :
      D (g (A.upperCutCircle i q)) 2 = A.upperCut := (hD _).trans (hheight i q)
  have hcover : (⋃ i, range (A.upperCutCircle i)) = {p : S2 | g p 2 = A.upperCut} := by
    simpa [axis, PiLp.inner_apply] using A.iUnion_range_upperCutCircle
  refine ⟨?_, ?_, ?_⟩
  · intro i
    obtain ⟨hs, hi, hd⟩ := A.upperCutCircle_geometry i
    apply smooth_projection_circle (D.contMDiff.comp (hg.contMDiff.comp hs))
      (D.injective.comp (hg.isEmbedding.injective.comp hi)) _ (hheightD i)
    intro q
    rw [mfderiv_comp q (D.contMDiff.mdifferentiable (by simp) _)
      ((hg.contMDiff.comp hs).mdifferentiable (by simp) q),
      mfderiv_comp q (hg.contMDiff.mdifferentiable (by simp) _)
        (hs.mdifferentiable (by simp) q)]
    exact (D.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
      ((injective_mfderiv_sphere_embedding hg _).comp (hd q))
  · intro x y hxy
    apply A.upperCutCircle_joint_injective
    apply hg.isEmbedding.injective
    apply D.injective
    calc
      D (g (A.upperCutCircle x.1 x.2)) = toE3 (upperPlanarCutCircle A D x.1 x.2) A.upperCut :=
        (toE3_toE2_of_height (hheightD x.1 x.2)).symm
      _ = toE3 (upperPlanarCutCircle A D y.1 y.2) A.upperCut :=
        congrArg (fun z => toE3 z A.upperCut) hxy
      _ = D (g (A.upperCutCircle y.1 y.2)) := toE3_toE2_of_height (hheightD y.1 y.2)
  · ext x
    constructor
    · intro hx
      obtain ⟨i, q, rfl⟩ := mem_iUnion.mp hx
      exact ⟨A.upperCutCircle i q, (toE3_toE2_of_height (hheightD i q)).symm⟩
    · rintro ⟨p, hp⟩
      have hph : g p 2 = A.upperCut := by
        have hp2 := congrArg (fun y : E3 => y 2) hp
        change D (g p) 2 = A.upperCut at hp2
        exact (hD _).symm.trans hp2
      obtain ⟨i, q, hq⟩ := mem_iUnion.mp (hcover.superset hph)
      apply mem_iUnion_of_mem i
      refine ⟨q, ?_⟩
      dsimp [upperPlanarCutCircle]
      rw [hq]
      have hproj := congrArg toE2 hp
      simpa only [Function.comp_apply, toE2_toE3'] using hproj

private theorem exists_one_upperPlanarCutCircle {g : S2 → E3} {B : Set Real} {K : Set S2}
    (A : AnnularEndFamily axis g B K)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hD : ∀ y, D y 2 = y 2) (hcard : Nat.card A.UpperCutIndex = 1) :
    ∃ c : S1 → E2,
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ c ∧
      range c = {x : E2 | toE3 x A.upperCut ∈ range (D ∘ g)} ∧
      ∀ Q : Set S2, Q ⊆ {p : S2 | g p 2 = A.upperCut} →
        (fun p => toE2 (D (g p))) '' Q ⊆ range c := by
  obtain ⟨i, hi⟩ := Nat.card_eq_one_iff_exists.mp hcard
  obtain ⟨hemb, _, hcover⟩ := upperPlanarCutCircle_geometry A hg D hD
  have hfull : range (upperPlanarCutCircle A D i) =
      {x : E2 | toE3 x A.upperCut ∈ range (D ∘ g)} := by
    rw [← hcover]
    apply Subset.antisymm (subset_iUnion _ i)
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    simpa only [hi j] using hj
  refine ⟨upperPlanarCutCircle A D i, hemb i, hfull, ?_⟩
  intro Q hQ x hx
  rw [hfull]
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨p, (toE3_toE2_of_height ((hD _).trans (hQ hp))).symm⟩

theorem exists_actual_positive_cut_circle_of_single_upper_end
    {g : S2 → E3} {B : Set Real} {K : Set S2}
    (A : AnnularEndFamily axis g B K)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hD : ∀ y, D y 2 = y 2) (hcard : Nat.card A.UpperCutIndex = 1)
    (e : OpenPartialHomeomorph E2 S2) {r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2)
    (hrs : SaddleLevel.closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, g (e x) 2 = -(x 0)^2 + (x 1)^2)
    (hcut : A.upperCut = t) :
    ∃ c : S1 → E2,
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ c ∧
      ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞
        (fun z : Real × S1 => c z.2) ∧
      range c = {x : E2 | toE3 x t ∈ range (D ∘ g)} ∧
      ∀ i, (fun p => toE2 (D (g p))) '' SaddleLevel.positivePatchArc e r t i ⊆
        range c := by
  obtain ⟨c, hc, hfull, hsub⟩ := exists_one_upperPlanarCutCircle A hg D hD hcard
  refine ⟨c, hc, hc.contMDiff.comp contMDiff_snd, by simpa only [hcut] using hfull, ?_⟩
  intro i
  apply hsub
  intro p hp
  have heq := SaddleLevel.positive_patch_level_eq_arcs (h := fun p : S2 => g p 2)
    (c := 0) e hr ht htr hrs (fun x hx => by simpa only [zero_sub] using hform x hx)
  have hlev := (heq.superset (mem_iUnion_of_mem i hp)).2
  change g p 2 = A.upperCut
  simpa only [mem_preimage, mem_singleton_iff, zero_add, hcut] using hlev

private def lowerPlanarCutCircle {g : S2 → E3} {B : Set Real} {K : Set S2}
    (A : AnnularEndFamily axis g B K)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (i : A.LowerCutIndex) (q : S1) : E2 :=
  toE2 (D (g (A.lowerCutCircle i q)))

private theorem lowerPlanarCutCircle_geometry {g : S2 → E3} {B : Set Real} {K : Set S2}
    (A : AnnularEndFamily axis g B K)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hD : ∀ y, D y 2 = y 2) :
    (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞
      (lowerPlanarCutCircle A D i)) ∧
    Injective (fun z : A.LowerCutIndex × S1 => lowerPlanarCutCircle A D z.1 z.2) ∧
    (⋃ i, range (lowerPlanarCutCircle A D i)) =
      {x : E2 | toE3 x A.lowerCut ∈ range (D ∘ g)} := by
  have hheight (i : A.LowerCutIndex) (q : S1) :
      g (A.lowerCutCircle i q) 2 = A.lowerCut := by
    simpa [axis, PiLp.inner_apply] using A.lowerCutCircle_height i q
  have hheightD (i : A.LowerCutIndex) (q : S1) :
      D (g (A.lowerCutCircle i q)) 2 = A.lowerCut := (hD _).trans (hheight i q)
  have hcover : (⋃ i, range (A.lowerCutCircle i)) = {p : S2 | g p 2 = A.lowerCut} := by
    simpa [axis, PiLp.inner_apply] using A.iUnion_range_lowerCutCircle
  refine ⟨?_, ?_, ?_⟩
  · intro i
    obtain ⟨hs, hi, hd⟩ := A.lowerCutCircle_geometry i
    apply smooth_projection_circle (D.contMDiff.comp (hg.contMDiff.comp hs))
      (D.injective.comp (hg.isEmbedding.injective.comp hi)) _ (hheightD i)
    intro q
    rw [mfderiv_comp q (D.contMDiff.mdifferentiable (by simp) _)
      ((hg.contMDiff.comp hs).mdifferentiable (by simp) q),
      mfderiv_comp q (hg.contMDiff.mdifferentiable (by simp) _)
        (hs.mdifferentiable (by simp) q)]
    exact (D.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
      ((injective_mfderiv_sphere_embedding hg _).comp (hd q))
  · intro x y hxy
    apply A.lowerCutCircle_joint_injective
    apply hg.isEmbedding.injective
    apply D.injective
    calc
      D (g (A.lowerCutCircle x.1 x.2)) = toE3 (lowerPlanarCutCircle A D x.1 x.2) A.lowerCut :=
        (toE3_toE2_of_height (hheightD x.1 x.2)).symm
      _ = toE3 (lowerPlanarCutCircle A D y.1 y.2) A.lowerCut :=
        congrArg (fun z => toE3 z A.lowerCut) hxy
      _ = D (g (A.lowerCutCircle y.1 y.2)) := toE3_toE2_of_height (hheightD y.1 y.2)
  · ext x
    constructor
    · intro hx
      obtain ⟨i, q, rfl⟩ := mem_iUnion.mp hx
      exact ⟨A.lowerCutCircle i q, (toE3_toE2_of_height (hheightD i q)).symm⟩
    · rintro ⟨p, hp⟩
      have hph : g p 2 = A.lowerCut := by
        have hp2 := congrArg (fun y : E3 => y 2) hp
        change D (g p) 2 = A.lowerCut at hp2
        exact (hD _).symm.trans hp2
      obtain ⟨i, q, hq⟩ := mem_iUnion.mp (hcover.superset hph)
      apply mem_iUnion_of_mem i
      refine ⟨q, ?_⟩
      dsimp [lowerPlanarCutCircle]
      rw [hq]
      have hproj := congrArg toE2 hp
      simpa only [Function.comp_apply, toE2_toE3'] using hproj

private theorem exists_two_lowerPlanarCutCircles {g : S2 → E3} {B : Set Real} {K : Set S2}
    (A : AnnularEndFamily axis g B K)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hD : ∀ y, D y 2 = y 2) (E : Fin 2 ≃ A.LowerCutIndex)
    (Q : Fin 2 → Set S2) (hQ : ∀ i, Q i ⊆ range (A.lowerCutCircle (E i))) :
    ∃ c : Fin 2 → S1 → E2,
      (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (c i)) ∧
      Disjoint (range (c 0)) (range (c 1)) ∧
      (⋃ i, range (c i)) = {x : E2 | toE3 x A.lowerCut ∈ range (D ∘ g)} ∧
      ∀ i, (fun p => toE2 (D (g p))) '' Q i ⊆ range (c i) := by
  obtain ⟨hemb, hinj, hcover⟩ := lowerPlanarCutCircle_geometry A hg D hD
  refine ⟨fun i => lowerPlanarCutCircle A D (E i), fun i => hemb _, ?_, ?_, ?_⟩
  · apply disjoint_left.mpr
    rintro x ⟨p, hp⟩ ⟨q, hq⟩
    have hindices : (E 0, p) = (E 1, q) := hinj (hp.trans hq.symm)
    have heq : E 0 = E 1 := congrArg Prod.fst hindices
    exact (by decide : (0 : Fin 2) ≠ 1) (E.injective heq)
  · rw [← hcover]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion_of_mem (E i) hi
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      obtain ⟨j, rfl⟩ := E.surjective i
      exact mem_iUnion_of_mem j hi
  · intro i x hx
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hQ i hp
    exact mem_range_self q

private theorem exists_actual_negative_cut_pair_of_resolved_components
    {g : S2 → E3} {B : Set Real} {K : Set S2}
    (A : AnnularEndFamily axis g B K)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hD : ∀ y, D y 2 = y 2)
    (e : OpenPartialHomeomorph E2 S2) {r t : Real}
    (_ht : 0 < t) (htr : t < r ^ 2) (hcut : A.lowerCut = -t)
    (hcard : Nat.card (ConnectedComponents {q : S2 | g q 2 = -t}) = 2)
    (C : Fin 2 → Set S2)
    (hC : ∀ i q, q ∈ C i → connectedComponentIn {q : S2 | g q 2 = -t} q = C i)
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hpatch : ∀ i, SaddleLevel.negativePatchArc e r t i ⊆ C i) :
    ∃ c : Fin 2 → S1 → E2,
      (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (c i)) ∧
      (∀ i, ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞
        (fun z : Real × S1 => c i z.2)) ∧
      Disjoint (range (c 0)) (range (c 1)) ∧
      (⋃ i, range (c i)) = {x : E2 | toE3 x (-t) ∈ range (D ∘ g)} ∧
      ∀ i, (fun p => toE2 (D (g p))) '' SaddleLevel.negativePatchArc e r t i ⊆
        range (c i) := by
  have hlevel : {q : S2 | inner Real axis (g q) = A.lowerCut} =
      {q : S2 | g q 2 = -t} := by
    ext q
    rw [hcut]
    simp [axis, PiLp.inner_apply]
  have hcardA : Nat.card (ConnectedComponents
      {q : S2 | inner Real axis (g q) = A.lowerCut}) = 2 := by
    rw [hlevel]
    exact hcard
  have hCA : ∀ i q, q ∈ C i → connectedComponentIn
      {q : S2 | inner Real axis (g q) = A.lowerCut} q = C i := by
    rw [hlevel]
    exact hC
  have hzero : 0 ∈ Icc (-SaddleLevel.hyperbolaRadius r t) (SaddleLevel.hyperbolaRadius r t) :=
    ⟨neg_nonpos.mpr (SaddleLevel.hyperbolaRadius_pos htr).le,
      (SaddleLevel.hyperbolaRadius_pos htr).le⟩
  obtain ⟨E, hE⟩ := A.exists_lowerCutCircle_equiv_of_two_components hcardA C hCA hdisjoint
    (fun i => e (SaddleLevel.negativeLevelArc t i 0))
    (fun i => hpatch i (mem_image_of_mem e (mem_image_of_mem _ hzero)))
  obtain ⟨c, hc, hdisj, hfull, hsub⟩ := exists_two_lowerPlanarCutCircles A hg D hD E
    (SaddleLevel.negativePatchArc e r t) (fun i => (hpatch i).trans (hE i).superset)
  exact ⟨c, hc, fun i => (hc i).contMDiff.comp contMDiff_snd, hdisj,
    by simpa only [hcut] using hfull, hsub⟩

theorem exists_uniform_actual_negative_cut_pairs
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (haxis : (M.v : E3) = axis) (hzero : g p 2 = 0)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (hD : ∀ y, D y 2 = y 2)
    (e : OpenPartialHomeomorph E2 S2) {r eta : Real} (hr : 0 < r) (heta : 0 < eta)
    (hresolved : ∀ t : Real, 0 < t → t ≤ eta →
      Nat.card (ConnectedComponents {q : S2 | g q 2 = -t}) = 2 ∧
      ∃ C : Fin 2 → Set S2,
        Pairwise (fun i j => Disjoint (C i) (C j)) ∧
        (∀ i, SaddleLevel.negativePatchArc e r t i ⊆ C i) ∧
        ∀ i q, q ∈ C i → connectedComponentIn {q : S2 | g q 2 = -t} q = C i) :
    ∃ delta : Real, 0 < delta ∧ delta ≤ eta ∧ delta < r ^ 2 ∧
      ∀ t : Real, 0 < t → t ≤ delta →
        ∃ c : Fin 2 → S1 → E2,
          (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (c i)) ∧
          (∀ i, ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞
            (fun z : Real × S1 => c i z.2)) ∧
          Disjoint (range (c 0)) (range (c 1)) ∧
          (⋃ i, range (c i)) = {x : E2 | toE3 x (-t) ∈ range (D ∘ g)} ∧
          ∀ i, (fun p => toE2 (D (g p))) '' SaddleLevel.negativePatchArc e r t i ⊆
            range (c i) := by
  obtain ⟨eps, heps, hfamilies⟩ := M.exists_terminal_annular_end_family hg P hP hcaps hp hc
  let delta := min eta (min eps (r ^ 2)) / 2
  have hmin : 0 < min eta (min eps (r ^ 2)) := lt_min heta (lt_min heps (sq_pos_of_pos hr))
  have hdelta : 0 < delta := half_pos hmin
  have hdm : delta < min eta (min eps (r ^ 2)) := half_lt_self hmin
  have hdeta : delta ≤ eta := hdm.le.trans (min_le_left _ _)
  have hdeps : delta ≤ eps := hdm.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdr : delta < r ^ 2 := hdm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨delta, hdelta, hdeta, hdr, ?_⟩
  intro t ht htd
  let B0 := (fun q => inner Real (M.v : E3) (M.D (f q))) ''
    {q | mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0}
  let K0 := P.core
  have hAt : ∃ A : AnnularEndFamily axis g B0 K0,
      A.lowerCut = -t ∧ A.upperCut = t := by
    have hh : ∃ A : AnnularEndFamily (M.v : E3) g B0 K0,
        A.lowerCut = inner Real (M.v : E3) (g p) - t ∧
        A.upperCut = inner Real (M.v : E3) (g p) + t :=
      hfamilies t ht (htd.trans hdeps)
    rw [haxis] at hh
    simpa [axis, PiLp.inner_apply, hzero] using hh
  obtain ⟨A, hAlower, _⟩ := hAt
  obtain ⟨hcard, C, hdisjoint, hpatch, hC⟩ := hresolved t ht (htd.trans hdeta)
  exact exists_actual_negative_cut_pair_of_resolved_components A
    (M.tree.embedding_of_mem_leaves hg) D hD e ht (htd.trans_lt hdr) hAlower
    hcard C hC hdisjoint hpatch

private theorem exists_open_connected_trace_neighborhood
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyConnectedSpace X] {f : X → Y} (hf : _root_.Topology.IsEmbedding f)
    {K U : Set Y} (hK : IsConnected K) (hKr : K ⊆ range f)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ N : Set Y, IsOpen N ∧ K ⊆ N ∧ N ⊆ U ∧ IsConnected (N ∩ range f) := by
  obtain ⟨y, hy⟩ := hK.nonempty
  obtain ⟨x, rfl⟩ := hKr hy
  have hpre : IsPreconnected (f ⁻¹' K) := hf.isInducing.isPreconnected_image.mp (by
    rw [image_preimage_eq_of_subset hKr]
    exact hK.isPreconnected)
  let A := connectedComponentIn (f ⁻¹' U) x
  have hxU : x ∈ f ⁻¹' U := hKU hy
  have hA : IsOpen A := (hU.preimage hf.continuous).connectedComponentIn
  have hKA : f ⁻¹' K ⊆ A := hpre.subset_connectedComponentIn hy
    (preimage_mono hKU)
  have hAconn : IsConnected A := isConnected_connectedComponentIn_iff.mpr hxU
  obtain ⟨W, hW, htrace⟩ := hf.isInducing.image_eq_isOpen_inter_range hA
  refine ⟨W ∩ U, hW.inter hU, ?_, inter_subset_right, ?_⟩
  · intro y hyK
    obtain ⟨z, rfl⟩ := hKr hyK
    refine ⟨?_, hKU hyK⟩
    exact ((congrArg (fun S : Set Y => f z ∈ S) htrace).mp
      (mem_image_of_mem f (hKA hyK))).1
  · have heq : (W ∩ U) ∩ range f = f '' A := by
      rw [htrace]
      apply Subset.antisymm
      · exact fun _ hy => ⟨hy.1.1, hy.2⟩
      · intro y hy
        have hyA : y ∈ f '' A := htrace.symm ▸ hy
        obtain ⟨z, hz, rfl⟩ := hyA
        exact ⟨⟨hy.1, connectedComponentIn_subset (f ⁻¹' U) x hz⟩, hy.2⟩
    rw [heq]
    exact hAconn.image f hf.continuous.continuousOn

private theorem exists_common_open_connected_pair_neighborhood
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [LocallyConnectedSpace X] [T2Space Y]
    (c d : Fin 2 → X → Y)
    (hc : ∀ i, _root_.Topology.IsEmbedding (c i)) (hd : ∀ i, _root_.Topology.IsEmbedding (d i))
    (hcdis : Disjoint (range (c 0)) (range (c 1)))
    (hddis : Disjoint (range (d 0)) (range (d 1)))
    (K : Fin 2 → Set Y) (hK : ∀ i, IsConnected (K i))
    (hKc : ∀ i, K i ⊆ range (c i)) (hKd : ∀ i, K i ⊆ range (d i))
    {C U : Set Y} (hU : IsOpen U) (hCU : C ⊆ U) (hKU : ∀ i, K i ⊆ U)
    (hcommon : U ∩ (range (c 0) ∪ range (c 1)) =
      U ∩ (range (d 0) ∪ range (d 1)))
    (hcover : C ∩ (range (c 0) ∪ range (c 1)) ⊆ K 0 ∪ K 1) :
    ∃ N : Set Y, IsOpen N ∧ C ⊆ N ∧ N ⊆ U ∧
      ∀ i, IsConnected (N ∩ range (c i)) ∧ N ∩ range (c i) = N ∩ range (d i) := by
  have hcclosed (i : Fin 2) : IsClosed (range (c i)) :=
    (isCompact_range (hc i).continuous).isClosed
  have hdclosed (i : Fin 2) : IsClosed (range (d i)) :=
    (isCompact_range (hd i).continuous).isClosed
  obtain ⟨N0, hN0, hKN0, hN0U, hconn0⟩ :=
    exists_open_connected_trace_neighborhood (hc 0) (hK 0) (hKc 0)
      (hU.sdiff ((hcclosed 1).union (hdclosed 1))) (by
        intro x hx
        refine ⟨hKU 0 hx, ?_⟩
        rintro (hxc | hxd)
        · exact disjoint_left.mp hcdis (hKc 0 hx) hxc
        · exact disjoint_left.mp hddis (hKd 0 hx) hxd)
  obtain ⟨N1, hN1, hKN1, hN1U, hconn1⟩ :=
    exists_open_connected_trace_neighborhood (hc 1) (hK 1) (hKc 1)
      (hU.sdiff ((hcclosed 0).union (hdclosed 0))) (by
        intro x hx
        refine ⟨hKU 1 hx, ?_⟩
        rintro (hxc | hxd)
        · exact disjoint_left.mp hcdis hxc (hKc 1 hx)
        · exact disjoint_left.mp hddis hxd (hKd 1 hx))
  have hlocal0 : N0 ∩ range (c 0) = N0 ∩ range (d 0) := by
    ext x
    constructor
    · rintro ⟨hxN, hxc⟩
      refine ⟨hxN, ?_⟩
      rcases (hcommon.subset ⟨(hN0U hxN).1, Or.inl hxc⟩).2 with hxd | hxd
      · exact hxd
      · exact ((hN0U hxN).2 (Or.inr hxd)).elim
    · rintro ⟨hxN, hxd⟩
      refine ⟨hxN, ?_⟩
      rcases (hcommon.superset ⟨(hN0U hxN).1, Or.inl hxd⟩).2 with hxc | hxc
      · exact hxc
      · exact ((hN0U hxN).2 (Or.inl hxc)).elim
  have hlocal1 : N1 ∩ range (c 1) = N1 ∩ range (d 1) := by
    ext x
    constructor
    · rintro ⟨hxN, hxc⟩
      refine ⟨hxN, ?_⟩
      rcases (hcommon.subset ⟨(hN1U hxN).1, Or.inr hxc⟩).2 with hxd | hxd
      · exact ((hN1U hxN).2 (Or.inr hxd)).elim
      · exact hxd
    · rintro ⟨hxN, hxd⟩
      refine ⟨hxN, ?_⟩
      rcases (hcommon.superset ⟨(hN1U hxN).1, Or.inr hxd⟩).2 with hxc | hxc
      · exact ((hN1U hxN).2 (Or.inl hxc)).elim
      · exact hxc
  let O := U \ (range (c 0) ∪ range (c 1))
  have hO : IsOpen O := hU.sdiff ((hcclosed 0).union (hcclosed 1))
  have hOd {x : Y} (hx : x ∈ O) : x ∉ range (d 0) ∪ range (d 1) := by
    intro hd'
    exact hx.2 ((hcommon.superset ⟨hx.1, hd'⟩).2)
  let N := N0 ∪ N1 ∪ O
  have hNc0 : N ∩ range (c 0) = N0 ∩ range (c 0) := by
    ext x
    constructor
    · rintro ⟨((h0 | h1) | ho), hxc⟩
      · exact ⟨h0, hxc⟩
      · exact ((hN1U h1).2 (Or.inl hxc)).elim
      · exact (ho.2 (Or.inl hxc)).elim
    · exact fun hx => ⟨Or.inl (Or.inl hx.1), hx.2⟩
  have hNc1 : N ∩ range (c 1) = N1 ∩ range (c 1) := by
    ext x
    constructor
    · rintro ⟨((h0 | h1) | ho), hxc⟩
      · exact ((hN0U h0).2 (Or.inl hxc)).elim
      · exact ⟨h1, hxc⟩
      · exact (ho.2 (Or.inr hxc)).elim
    · exact fun hx => ⟨Or.inl (Or.inr hx.1), hx.2⟩
  have hNd0 : N ∩ range (d 0) = N0 ∩ range (d 0) := by
    ext x
    constructor
    · rintro ⟨((h0 | h1) | ho), hxd⟩
      · exact ⟨h0, hxd⟩
      · exact ((hN1U h1).2 (Or.inr hxd)).elim
      · exact (hOd ho (Or.inl hxd)).elim
    · exact fun hx => ⟨Or.inl (Or.inl hx.1), hx.2⟩
  have hNd1 : N ∩ range (d 1) = N1 ∩ range (d 1) := by
    ext x
    constructor
    · rintro ⟨((h0 | h1) | ho), hxd⟩
      · exact ((hN0U h0).2 (Or.inr hxd)).elim
      · exact ⟨h1, hxd⟩
      · exact (hOd ho (Or.inr hxd)).elim
    · exact fun hx => ⟨Or.inl (Or.inr hx.1), hx.2⟩
  refine ⟨N, (hN0.union hN1).union hO, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxc : x ∈ range (c 0) ∪ range (c 1)
    · rcases hcover ⟨hx, hxc⟩ with h0 | h1
      · exact Or.inl (Or.inl (hKN0 h0))
      · exact Or.inl (Or.inr (hKN1 h1))
    · exact Or.inr ⟨hCU hx, hxc⟩
  · rintro x ((h0 | h1) | ho)
    · exact (hN0U h0).1
    · exact (hN1U h1).1
    · exact ho.1
  · intro i
    fin_cases i
    · change IsConnected (N ∩ range (c 0)) ∧ N ∩ range (c 0) = N ∩ range (d 0)
      rw [hNc0, hNd0]
      exact ⟨hconn0, hlocal0⟩
    · change IsConnected (N ∩ range (c 1)) ∧ N ∩ range (c 1) = N ∩ range (d 1)
      rw [hNc1, hNd1]
      exact ⟨hconn1, hlocal1⟩

private theorem exists_smooth_band_time_retraction {r δ : Real} (hr : 0 ≤ r) (hδ : 0 < δ) :
    ∃ θ : Real → Real, ContDiff Real ∞ θ ∧
      (∀ t, θ t ∈ Ioo (-δ) (r + δ)) ∧ ∀ t ∈ Icc (0 : Real) r, θ t = t := by
  obtain ⟨τ, hτ, hτrange, hτone, hτzero⟩ :=
    Plane.exists_smooth_interval_cutoff 0 r (half_pos hδ)
  refine ⟨fun t => τ t * t, hτ.mul contDiff_id, ?_, ?_⟩
  · intro t
    change τ t * t ∈ Ioo (-δ) (r + δ)
    by_cases ht : t ≤ -(δ / 2) ∨ r + δ / 2 ≤ t
    · rw [hτzero t (by simpa only [zero_sub] using ht), zero_mul]
      constructor <;> linarith
    · push Not at ht
      obtain ⟨hτ₀, hτ₁⟩ := hτrange t
      by_cases ht₀ : 0 ≤ t
      · have hl : 0 ≤ τ t * t := mul_nonneg hτ₀ ht₀
        have hu : τ t * t ≤ t := by nlinarith
        constructor <;> linarith [ht.2]
      · have hl : t ≤ τ t * t := by nlinarith
        have hu : τ t * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hτ₀ (le_of_not_ge ht₀)
        constructor <;> linarith [ht.1]
  · intro t ht
    change τ t * t = t
    rw [hτone t ht, one_mul]

private theorem exists_circle_families_on_regular_sphere_band
    {ι : Type*} {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {a b : Real} (hab : a ≤ b)
    (hregular : ∀ q : S2, h q ∈ Icc a b → mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0)
    (γ : ι → S1 → S2) (hγ : ∀ i, ContMDiff (𝓡 1) (𝓡 2) ∞ (γ i))
    (hγinj : Injective (fun z : ι × S1 => γ z.1 z.2))
    (hγder : ∀ i q, Injective (mfderiv (𝓡 1) (𝓡 2) (γ i) q))
    (hcover : (⋃ i, range (γ i)) = h ⁻¹' {a}) :
    ∃ F : ι → Real × S1 → S2,
      (∀ i, ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞ (F i)) ∧
      (∀ i q, F i (0, q) = γ i q) ∧
      ∀ t ∈ Icc (0 : Real) (b - a),
        (∀ i q, h (F i (t, q)) = a + t) ∧
        Injective (fun z : ι × S1 => F z.1 (t, z.2)) ∧
        (∀ i q, Injective (mfderiv (𝓡 1) (𝓡 2) (fun z => F i (t, z)) q)) ∧
        (⋃ i, range (fun q => F i (t, q))) = h ⁻¹' {a + t} := by
  obtain ⟨U, _, _, _, hfull, hreg, V, δ, Φ, hV, hbottom, _, hδ,
    hΦ, hΦzero, _, hlevels⟩ :=
    exists_sphere_height_level_diffeomorphisms_on_regular_band_of_smooth hh hab hregular
  let := openLevelSetChartedSpace hh U hreg 1 a
  let := isManifold_openLevelSet hh U hreg 1 a
  have hγa (i : ι) (q : S1) : h (γ i q) = a := by
    change γ i q ∈ h ⁻¹' {a}
    exact hcover ▸ mem_iUnion_of_mem i (mem_range_self q)
  have hγU (i : ι) (q : S1) : γ i q ∈ U :=
    (inter_eq_right.mp (hfull a ⟨le_rfl, hab⟩)) (hγa i q)
  let J : ι → S1 → openLevelSet h U a := fun i q => ⟨⟨γ i q, hγU i q⟩, hγa i q⟩
  have hJ (i : ι) : ContMDiff (𝓡 1) (𝓡 1) ∞ (J i) := by
    intro q
    exact (contMDiffAt_into_openLevelSet_iff hh 1 a U hreg (J i) q).mpr (hγ i q)
  have hJder (i : ι) (q : S1) : Injective (mfderiv (𝓡 1) (𝓡 1) (J i) q) := by
    have hcomp : openLevelIncl h U a ∘ J i = γ i := rfl
    have hd := hγder i q
    rw [← hcomp, mfderiv_comp q
      ((contMDiff_openLevelIncl hh U hreg 1 a).mdifferentiable (by simp) _)
      ((hJ i).mdifferentiable (by simp) _)] at hd
    intro v w hvw
    apply hd
    exact congrArg (mfderiv (𝓡 1) (𝓡 2) (openLevelIncl h U a) (J i q)) hvw
  obtain ⟨θ, hθ, hθrange, hθid⟩ := exists_smooth_band_time_retraction (sub_nonneg.mpr hab) hδ
  let F : ι → Real × S1 → S2 := fun i z => Φ (θ z.1, γ i z.2)
  have hF (i : ι) : ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞ (F i) := by
    apply contMDiffOn_univ.mp
    apply hΦ.comp ((hθ.contMDiff.comp contMDiff_fst).prodMk
      ((hγ i).comp contMDiff_snd)).contMDiffOn
    intro z _
    exact ⟨hθrange z.1, hbottom ⟨hγU i z.2, hγa i z.2⟩⟩
  refine ⟨F, hF, ?_, ?_⟩
  · intro i q
    dsimp [F]
    rw [hθid 0 ⟨le_rfl, sub_nonneg.mpr hab⟩]
    exact hΦzero _ (hbottom ⟨hγU i q, hγa i q⟩)
  · intro t ht
    have hat : a + t ∈ Icc a b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    let := openLevelSetChartedSpace hh U hreg 1 (a + t)
    let := isManifold_openLevelSet hh U hreg 1 (a + t)
    obtain ⟨et, het⟩ := hlevels (a + t) hat
    have heq (i : ι) : (fun q => F i (t, q)) = openLevelIncl h U (a + t) ∘ et ∘ J i := by
      funext q
      dsimp [F]
      rw [hθid t ht]
      simpa only [add_sub_cancel_left, J, openLevelIncl] using (het (J i q)).symm
    have heqp (i : ι) (q : S1) :
        F i (t, q) = openLevelIncl h U (a + t) (et (J i q)) := congrFun (heq i) q
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i q
      rw [heqp i q]
      exact (et (J i q)).property
    · rintro ⟨i, q⟩ ⟨j, z⟩ he
      apply hγinj
      have he' : openLevelIncl h U (a + t) (et (J i q)) =
          openLevelIncl h U (a + t) (et (J j z)) := by
        rw [← heqp i q, ← heqp j z]
        exact he
      have hj := et.injective ((isEmbedding_openLevelIncl h U (a + t)).injective he')
      exact congrArg (openLevelIncl h U a) hj
    · intro i q
      rw [heq i, mfderiv_comp q
        ((contMDiff_openLevelIncl hh U hreg 1 (a + t)).mdifferentiable (by simp) _)
        ((et.contMDiff.comp (hJ i)).mdifferentiable (by simp) _),
        mfderiv_comp q (et.contMDiff.mdifferentiable (by simp) _)
          ((hJ i).mdifferentiable (by simp) _)]
      exact (injective_mfderiv_openLevelIncl hh U hreg 1 (a + t) _).comp
        ((et.mfderivToContinuousLinearEquiv (by simp) _).injective.comp (hJder i q))
    · ext q
      constructor
      · intro hq
        obtain ⟨i, z, rfl⟩ := mem_iUnion.mp hq
        change F i (t, z) ∈ h ⁻¹' {a + t}
        rw [heqp i z]
        exact (et (J i z)).property
      · intro hq
        let qt : openLevelSet h U (a + t) :=
          ⟨⟨q, (inter_eq_right.mp (hfull (a + t) hat)) hq⟩, hq⟩
        have hqa : openLevelIncl h U a (et.symm qt) ∈ h ⁻¹' {a} := (et.symm qt).property
        rw [← hcover] at hqa
        obtain ⟨i, z, hz⟩ := mem_iUnion.mp hqa
        refine mem_iUnion_of_mem i ⟨z, ?_⟩
        change F i (t, z) = q
        rw [heqp i z]
        have hJz : J i z = et.symm qt :=
          (isEmbedding_openLevelIncl h U a).injective hz
        change openLevelIncl h U (a + t) (et (J i z)) = q
        rw [hJz, et.apply_symm_apply]
        rfl

private theorem sphere_ambient_mfderiv_injective
    (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (p : S2) :
    Injective (mfderiv (𝓡 2) (𝓡 3) (fun q : S2 => G q) p) := by
  change Injective (mfderiv (𝓡 2) (𝓡 3) (G ∘ (Subtype.val : S2 → E3)) p)
  rw [mfderiv_comp p (G.contMDiff.mdifferentiable (by simp) (p : E3))
    ((contMDiff_coe_sphere (n := 2) (m := ∞) (E := E3) p).mdifferentiableAt (by simp))]
  apply (G.mfderivToContinuousLinearEquiv (by simp) (p : E3)).injective.comp
  convert! injective_mvfderiv_subtypeVal_sphere p

private theorem projected_lowerSourceCircle {S : Set E2} (hS : S ⊆ levelSet) :
    (fun p : S2 => toE2 (shear (3 / 10) p)) '' (lowerSphereMap '' S) = S := by
  have hfix (x : E2) (hx : x ∈ S) : toE2 (shear (3 / 10) (lowerSphereMap x)) = x := by
    ext i
    fin_cases i <;> simp [toE2, lowerSphereMap_coe (hS hx), lowerReconstruction]
  rw [image_image]
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    simpa only [hfix x hx] using hx
  · intro x hx
    exact ⟨x, hx, hfix x hx⟩

private theorem exists_nested_planar_circles_below_saddle
    {p : S2} (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0)
    (hpz : (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8))
    {a : Real} (ha : 1 ≤ a) (hap : a < height p) :
    ∃ β : Fin 2 → S1 → E2,
      (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (β i)) ∧
      Disjoint (range (β 0)) (range (β 1)) ∧
      (⋃ i, range (β i)) = {x : E2 | toE3 x a ∈ shear (3 / 10) '' sphere (0 : E3) 1} ∧
      ∃ A B : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        A '' sphere (0 : E2) 1 = range (β 0) ∧
        B '' sphere (0 : E2) 1 = range (β 1) ∧
        B '' closedBall (0 : E2) 1 ⊆ A '' ball (0 : E2) 1 := by
  classical
  choose γ hγ hγi hγd hγr using fun i : Fin 2 => exists_smooth_capCircle i.castSucc
  have hγr₀ : range (γ 0) = outerSourceCircle := hγr 0
  have hγr₁ : range (γ 1) = innerSourceCircle := hγr 1
  have hγdisj : Disjoint (range (γ 0)) (range (γ 1)) := by
    rw [hγr₀, hγr₁]
    exact disjoint_sourceCircles
  have hγinj : Injective (fun z : Fin 2 × S1 => γ z.1 z.2) := by
    rintro ⟨i, q⟩ ⟨j, z⟩ he
    have hij : i = j := by
      by_contra hn
      fin_cases i <;> fin_cases j
      · exact hn rfl
      · exact disjoint_left.mp hγdisj (mem_range_self q) ⟨z, he.symm⟩
      · exact disjoint_left.mp hγdisj (mem_range_self z) ⟨q, he⟩
      · exact hn rfl
    subst j
    exact Prod.ext rfl (hγi i he)
  have hγcover : (⋃ i, range (γ i)) = height ⁻¹' {(1 : Real)} := by
    rw [lower_height_level_eq_sourceCircles]
    ext q
    simp only [mem_iUnion, Fin.exists_fin_two, hγr₀, hγr₁, mem_union]
  have hregular (q : S2) (hq : height q ∈ Icc (1 : Real) a) :
      mfderiv (𝓡 2) 𝓘(Real, Real) height q ≠ 0 := by
    intro hqcrit
    have hqp := (critical_in_height_band_iff_eq_saddle hp hpz q
      ⟨hq.1, hq.2.trans (hap.le.trans
        (saddle_height_lt_fortyone_fortieths hp hpz).le) |>.trans (by norm_num)⟩).mp hqcrit
    subst q
    exact hap.not_ge hq.2
  obtain ⟨F, hF, hFzero, hFgeom⟩ := exists_circle_families_on_regular_sphere_band
    height_contMDiff ha hregular γ hγ hγinj hγd hγcover
  let G : S2 → E3 := fun q => shear (3 / 10) q
  have hG : ContMDiff (𝓡 2) (𝓡 3) ∞ G :=
    (shear (3 / 10)).contMDiff.comp (contMDiff_coe_sphere (n := 2) (m := ∞) (E := E3))
  let c : Fin 2 → Real → S1 → E2 := fun i u q => toE2 (G (F i (u, q)))
  have hc (i : Fin 2) : ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞
      (fun z : Real × S1 => c i z.1 z.2) :=
    contDiff_toE2.contMDiff.comp (hG.comp (hF i))
  have hheight (u : Real) (hu : u ∈ Icc (0 : Real) (a - 1)) (i : Fin 2) (q : S1) :
      G (F i (u, q)) 2 = 1 + u := (hFgeom u hu).1 i q
  have hci (u : Real) (hu : u ∈ Icc (0 : Real) (a - 1)) :
      Injective (fun z : Fin 2 × S1 => c z.1 u z.2) := by
    intro z w he
    apply (hFgeom u hu).2.1
    apply Subtype.ext
    apply (shear (3 / 10)).injective
    calc
      G (F z.1 (u, z.2)) = toE3 (c z.1 u z.2) (1 + u) :=
        (toE3_toE2_of_height (hheight u hu z.1 z.2)).symm
      _ = toE3 (c w.1 u w.2) (1 + u) := congrArg (fun x => toE3 x (1 + u)) he
      _ = G (F w.1 (u, w.2)) := toE3_toE2_of_height (hheight u hu w.1 w.2)
  have hcemb (i : Fin 2) (u : Real) (hu : u ∈ Icc (0 : Real) (a - 1)) :
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (c i u) := by
    have hslice : ContMDiff (𝓡 1) (𝓡 2) ∞ (fun q => F i (u, q)) :=
      (hF i).comp (contMDiff_const.prodMk contMDiff_id)
    apply smooth_projection_circle (hG.comp hslice)
      ((shear (3 / 10)).injective.comp (Subtype.val_injective.comp ?_)) ?_
      (hheight u hu i)
    · intro q z he
      exact congrArg Prod.snd ((hFgeom u hu).2.1 (a₁ := (i, q)) (a₂ := (i, z)) he)
    · intro q
      rw [mfderiv_comp q (hG.mdifferentiable (by simp) _) (hslice.mdifferentiable (by simp) _)]
      exact (sphere_ambient_mfderiv_injective (shear (3 / 10)) _).comp
        ((hFgeom u hu).2.2.1 i q)
  have hcdisj (u : Real) (hu : u ∈ Icc (0 : Real) (a - 1)) :
      Disjoint (range (c 0 u)) (range (c 1 u)) := by
    apply disjoint_left.mpr
    rintro x ⟨q, hq⟩ ⟨z, hz⟩
    have := congrArg Prod.fst (hci u hu (a₁ := (0, q)) (a₂ := (1, z)) (hq.trans hz.symm))
    exact (by decide : (0 : Fin 2) ≠ 1) this
  obtain ⟨K, _, Ψ, _, _, _, _, hΨ⟩ :=
    Plane.Isotopy.ArcPairs.exists_planar_circle_pair_family_extension
      (sub_nonneg.mpr ha) c hc hcemb hcdisj
  have hzero (i : Fin 2) : c i 0 = (fun q => toE2 (shear (3 / 10) (γ i q))) := by
    funext q
    dsimp [c, G]
    rw [hFzero]
  have hr₀ : range (c 0 0) = outerOval := by
    rw [hzero 0]
    change range ((fun p : S2 => toE2 (shear (3 / 10) p)) ∘ γ 0) = _
    rw [range_comp, hγr₀]
    apply projected_lowerSourceCircle
    rw [levelSet_eq_outerOval_union_innerOval]
    exact subset_union_left
  have hr₁ : range (c 1 0) = innerOval := by
    rw [hzero 1]
    change range ((fun p : S2 => toE2 (shear (3 / 10) p)) ∘ γ 1) = _
    rw [range_comp, hγr₁]
    apply projected_lowerSourceCircle
    rw [levelSet_eq_outerOval_union_innerOval]
    exact subset_union_right
  have hu : a - 1 ∈ Icc (0 : Real) (a - 1) := ⟨sub_nonneg.mpr ha, le_rfl⟩
  have hΨrange (i : Fin 2) : Ψ (a - 1) '' range (c i 0) = range (c i (a - 1)) := by
    rw [← range_comp]
    exact congrArg range (funext (hΨ i (a - 1) hu))
  refine ⟨fun i => c i (a - 1), fun i => hcemb i _ hu, hcdisj _ hu, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨i, q, rfl⟩ := mem_iUnion.mp hx
      refine ⟨F i (a - 1, q), (F i (a - 1, q)).property, ?_⟩
      exact (toE3_toE2_of_height (by simpa only [add_sub_cancel] using hheight (a - 1) hu i q)).symm
    · rintro ⟨y, hy, he⟩
      have hya : height (⟨y, hy⟩ : S2) = 1 + (a - 1) := by
        change shear (3 / 10) y 2 = _
        rw [he]
        simp [toE3]
      have hcover := (hFgeom (a - 1) hu).2.2.2
      have hycov : (⟨y, hy⟩ : S2) ∈ ⋃ i, range (fun q => F i (a - 1, q)) := by
        rw [hcover]
        exact hya
      obtain ⟨i, q, hq⟩ := mem_iUnion.mp hycov
      refine mem_iUnion_of_mem i ⟨q, ?_⟩
      change toE2 (shear (3 / 10) (F i (a - 1, q))) = x
      change F i (a - 1, q) = (⟨y, hy⟩ : S2) at hq
      rw [hq]
      exact (congrArg toE2 he).trans (toE2_toE3' x a)
  · obtain ⟨A, B, hA, hB, _, hBA⟩ := exists_nested_filled_disks
    refine ⟨A.trans (Ψ (a - 1)), B.trans (Ψ (a - 1)), ?_, ?_, ?_⟩
    · change (Ψ (a - 1) ∘ A) '' sphere (0 : E2) 1 = _
      rw [image_comp, hA, ← hr₀, hΨrange]
    · change (Ψ (a - 1) ∘ B) '' sphere (0 : E2) 1 = _
      rw [image_comp, hB, ← hr₁, hΨrange]
    · change (Ψ (a - 1) ∘ B) '' closedBall (0 : E2) 1 ⊆
        (Ψ (a - 1) ∘ A) '' ball (0 : E2) 1
      rw [image_comp, image_comp]
      exact image_mono hBA

private theorem exists_planar_fiber_of_affine_height
    (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    {scale c : Real} (hscale : 0 < scale)
    (hheight : ∀ y : E3, G y 2 = scale * (y 2 - c)) (a : Real) :
    ∃ F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      ∀ x, toE3 (F x) (scale * (a - c)) = G (toE3 x a) := by
  let t := scale * (a - c)
  let f : E2 → E2 := fun x => toE2 (G (toE3 x a))
  let g : E2 → E2 := fun x => toE2 (G.symm (toE3 x t))
  have hfheight (x : E2) : G (toE3 x a) 2 = t := hheight _
  have hgheight (x : E2) : G.symm (toE3 x t) 2 = a := by
    have he := hheight (G.symm (toE3 x t))
    rw [G.apply_symm_apply] at he
    change scale * (a - c) = scale * ((G.symm (toE3 x t)) 2 - c) at he
    nlinarith
  have hleft : LeftInverse g f := by
    intro x
    dsimp [g, f]
    rw [toE3_toE2_of_height (hfheight x), G.symm_apply_apply, toE2_toE3']
  have hright : RightInverse g f := by
    intro x
    dsimp [g, f]
    rw [toE3_toE2_of_height (hgheight x), G.apply_symm_apply, toE2_toE3']
  let F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
    { toEquiv := ⟨f, g, hleft, hright⟩
      contMDiff_toFun :=
        (contDiff_toE2.comp (G.contMDiff.contDiff.comp (contDiff_toE3 a))).contMDiff
      contMDiff_invFun :=
        (contDiff_toE2.comp (G.symm.contMDiff.contDiff.comp (contDiff_toE3 t))).contMDiff }
  exact ⟨F, fun x => toE3_toE2_of_height (hfheight x)⟩

private theorem planar_fiber_image
    (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) {a t : Real}
    (hF : ∀ x, toE3 (F x) t = G (toE3 x a)) (S : Set E3) :
    F '' {x : E2 | toE3 x a ∈ S} = {x : E2 | toE3 x t ∈ G '' S} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨toE3 y a, hy, (hF y).symm⟩
  · rintro ⟨y, hy, he⟩
    refine ⟨F.symm x, ?_, F.apply_symm_apply x⟩
    have hxy : toE3 (F.symm x) a = y := by
      apply G.injective
      change G (toE3 (F.symm x) a) = G y
      rw [← hF, F.apply_symm_apply]
      exact he.symm
    change toE3 (F.symm x) a ∈ S
    exact hxy.symm ▸ hy

private theorem exists_flattened_nested_circles_negative_level
    (T D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ x : E3, D x 2 = x 2)
    {p : S2} (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0)
    (hpz : (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8))
    {scale t : Real} (hscale : 0 < scale) (ht : t < 0)
    (htlower : 1 ≤ height p + t / scale)
    (hTheight : ∀ y : E3, T y 2 = scale * (y 2 - height p)) :
    ∃ β : Fin 2 → S1 → E2,
      (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (β i)) ∧
      (∀ i, ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞
        (fun z : Real × S1 => β i z.2)) ∧
      Disjoint (range (β 0)) (range (β 1)) ∧
      (⋃ i, range (β i)) = {x : E2 | toE3 x t ∈
        (((shear (3 / 10)).trans T).trans D) '' sphere (0 : E3) 1} ∧
      ∃ A B : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        A '' sphere (0 : E2) 1 = range (β 0) ∧
        B '' sphere (0 : E2) 1 = range (β 1) ∧
        B '' closedBall (0 : E2) 1 ⊆ A '' ball (0 : E2) 1 := by
  let a := height p + t / scale
  have hap : a < height p := by
    have hneg := div_neg_of_neg_of_pos ht hscale
    dsimp [a]
    linarith
  obtain ⟨γ, hγ, hγdisj, hγcover, A, B, hA, hB, hBA⟩ :=
    exists_nested_planar_circles_below_saddle hp hpz htlower hap
  let G := T.trans D
  have hGheight (y : E3) : G y 2 = scale * (y 2 - height p) := by
    change D (T y) 2 = _
    rw [hDheight, hTheight]
  have hphysical : scale * (a - height p) = t := by dsimp [a]; field_simp; ring
  obtain ⟨F, hF⟩ := exists_planar_fiber_of_affine_height G hscale hGheight a
  rw [hphysical] at hF
  have hβ (i : Fin 2) : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (F ∘ γ i) := by
    apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
      (F.contMDiff.comp (hγ i).contMDiff) (F.injective.comp (hγ i).isEmbedding.injective)
    intro q
    rw [mfderiv_comp q (F.contMDiff.mdifferentiable (by simp) _)
      ((hγ i).contMDiff.mdifferentiable (by simp) _)]
    exact (F.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
      (((hγ i).isImmersion.isImmersionAt q).injective_mfderiv_modelWithCornersSelf (by simp))
  refine ⟨fun i => F ∘ γ i, hβ, fun i => (hβ i).contMDiff.comp contMDiff_snd, ?_, ?_,
    A.trans F, B.trans F, ?_, ?_, ?_⟩
  · rw [range_comp, range_comp]
    apply disjoint_left.mpr
    rintro x ⟨y, hy, hyx⟩ ⟨z, hz, hzx⟩
    have hyz : y = z := F.injective (hyx.trans hzx.symm)
    exact disjoint_left.mp hγdisj hy (hyz.symm ▸ hz)
  · simp only [range_comp]
    rw [← image_iUnion, hγcover, planar_fiber_image G F hF]
    rw [← image_comp]
    rfl
  · change (F ∘ A) '' sphere (0 : E2) 1 = range (F ∘ γ 0)
    rw [image_comp, hA, range_comp]
  · change (F ∘ B) '' sphere (0 : E2) 1 = range (F ∘ γ 1)
    rw [image_comp, hB, range_comp]
  · change (F ∘ B) '' closedBall (0 : E2) 1 ⊆ (F ∘ A) '' ball (0 : E2) 1
    rw [image_comp, image_comp]
    exact image_mono hBA

theorem exists_uniform_negative_nested_level_circles
    (T D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ x : E3, D x 2 = x 2)
    {p : S2} (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0)
    (hpz : (p : E3) 2 ∈ Ioo (3 / 5 : Real) (5 / 8))
    {scale : Real} (hscale : 0 < scale)
    (hTheight : ∀ y : E3, T y 2 = scale * (y 2 - height p)) :
    ∃ ε : Real, 0 < ε ∧ ∀ t ∈ Ico (-ε) (0 : Real),
      ∃ β : Fin 2 → S1 → E2,
        (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (β i)) ∧
        (∀ i, ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞
          (fun z : Real × S1 => β i z.2)) ∧
        Disjoint (range (β 0)) (range (β 1)) ∧
        (⋃ i, range (β i)) = {x : E2 | toE3 x t ∈
          (((shear (3 / 10)).trans T).trans D) '' sphere (0 : E3) 1} ∧
        ∃ A B : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          A '' sphere (0 : E2) 1 = range (β 0) ∧
          B '' sphere (0 : E2) 1 = range (β 1) ∧
          B '' closedBall (0 : E2) 1 ⊆ A '' ball (0 : E2) 1 := by
  obtain ⟨p₀, hp₀z, hp₀h, hp₀, _⟩ := exists_unique_critical_point_in_height_band
  have hp₀p : p₀ = p := critical_latitude_unique_in_saddle_interval hp₀ hp
    (Ioo_subset_Icc_self hp₀z) (Ioo_subset_Icc_self hpz)
  have hph : (1 : Real) < height p := hp₀p ▸ hp₀h.1
  refine ⟨scale * (height p - 1), mul_pos hscale (sub_pos.mpr hph), ?_⟩
  intro t ht
  apply exists_flattened_nested_circles_negative_level T D hDheight hp hpz hscale ht.2 _ hTheight
  have hdiv : 1 - height p ≤ t / scale := (le_div_iff₀ hscale).mpr (by nlinarith [ht.1])
  linarith

end RegularCircles

end Poincare.Manifold.Schoenflies.Saddle.Nested

end

end M38Schoenflies
