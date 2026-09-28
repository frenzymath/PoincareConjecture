import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.LocalParallel
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Rank
import Mathlib.Topology.Covering.Basic
import Mathlib.Data.Set.Card

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RicciFlow.Splitting

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

def UnitRicciKernel (D : LeviCivitaData g) :=
  {p : TangentBundle (𝓡 n) M |
    g.inner p.proj p.snd p.snd = 1 ∧ ∀ w, D.ricci p.proj p.snd w = 0}

instance (D : LeviCivitaData g) : TopologicalSpace (UnitRicciKernel D) :=
  inferInstanceAs (TopologicalSpace {p : TangentBundle (𝓡 n) M |
    g.inner p.proj p.snd p.snd = 1 ∧ ∀ w, D.ricci p.proj p.snd w = 0})

def unitRicciKernelProjection (D : LeviCivitaData g) (p : UnitRicciKernel D) : M := p.1.proj

theorem continuous_unitRicciKernelProjection (D : LeviCivitaData g) :
    Continuous (unitRicciKernelProjection D) :=
  (FiberBundle.continuous_proj (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))).comp
    continuous_subtype_val

theorem unit_ricci_null_eq_or_eq_neg (D : LeviCivitaData g) (x : M)
    (hdim : ricciNullity D x = 1) (v w : TangentSpace (𝓡 n) x)
    (hv : ∀ z, D.ricci x v z = 0) (hw : ∀ z, D.ricci x w z = 0)
    (hvu : g.inner x v v = 1) (hwu : g.inner x w w = 1) :
    w = v ∨ w = -v := by
  let v' : ricciKernel D x := ⟨v, (mem_ricciKernel D x v).mpr hv⟩
  have hv0 : v' ≠ 0 := by
    intro h
    have he : v = 0 := congrArg Subtype.val h
    simp only [he, map_zero] at hvu
    norm_num at hvu
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' v' hv0).mp hdim
    ⟨w, (mem_ricciKernel D x w).mpr hw⟩
  have hc' : c • v = w := congrArg Subtype.val hc
  have hc2 : c * c = 1 := by
    rw [← hc'] at hwu
    simpa only [map_smul, smul_apply, smul_eq_mul, hvu, mul_one] using hwu
  have hcpm : c = 1 ∨ c = -1 := by
    have : (c - 1) * (c + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases hcpm with rfl | rfl
  · exact Or.inl (by simpa only [one_smul] using hc'.symm)
  · exact Or.inr (by simpa only [neg_one_smul] using hc'.symm)

abbrev LineSign := ({1, -1} : Set ℝ)

instance : Fintype LineSign := ((Set.finite_singleton (-1 : ℝ)).insert 1).fintype

instance : DiscreteTopology LineSign := inferInstance

def unitRicciKernelLocalHomeomorph
    (D : LeviCivitaData g) {U : Set M}
    (V : (y : M) → TangentSpace (𝓡 n) y)
    (hV : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) U)
    (hdim : ∀ y ∈ U, ricciNullity D y = 1)
    (hunit : ∀ y ∈ U, g.inner y (V y) (V y) = 1)
    (hnull : ∀ y ∈ U, ∀ w, D.ricci y (V y) w = 0) :
    (unitRicciKernelProjection D ⁻¹' U) ≃ₜ U × LineSign := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let P := unitRicciKernelProjection D ⁻¹' U
  let q : P → ℝ := fun p => g.inner p.1.1.proj p.1.1.snd (V p.1.1.proj)
  have hpm (p : P) : p.1.1.snd = V p.1.1.proj ∨ p.1.1.snd = -V p.1.1.proj :=
    unit_ricci_null_eq_or_eq_neg D _ (hdim _ p.2) _ _ (hnull _ p.2) p.1.2.2
      (hunit _ p.2) p.1.2.1
  have hu (p : P) : g.inner p.1.1.proj (V p.1.1.proj) (V p.1.1.proj) = 1 :=
    hunit _ p.2
  have hq (p : P) : q p ∈ ({1, -1} : Set ℝ) := by
    change q p = 1 ∨ q p = -1
    rcases hpm p with h | h
    · exact Or.inl (by simp only [q, h, hu p])
    · exact Or.inr (by simp only [q, h, map_neg, neg_apply, hu p])
  let f : P → U × LineSign := fun p => ⟨⟨unitRicciKernelProjection D p.1, p.2⟩, ⟨q p, hq p⟩⟩
  let i : U × LineSign → P := fun z =>
    ⟨⟨⟨z.1.1, z.2.1 • V z.1.1⟩, by
      constructor
      · simp only [map_smul, smul_apply, smul_eq_mul, hunit _ z.1.2, mul_one]
        rcases z.2.2 with h | h
        · rw [h]; norm_num
        · rw [Set.mem_singleton_iff.mp h]; norm_num
      · intro w
        rw [← ricciBilinear_apply, map_smul, LinearMap.smul_apply, ricciBilinear_apply,
          hnull _ z.1.2 w, smul_zero]⟩, z.1.2⟩
  refine
    { toFun := f
      invFun := i
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · intro p
    apply Subtype.ext
    apply Subtype.ext
    change TotalSpace.mk _ (q p • V p.1.1.proj) = p.1.1
    have he : q p • V p.1.1.proj = p.1.1.snd := by
      rcases hpm p with h | h
      · simp only [q, h, hu p, one_smul]
      · simp only [q, h, map_neg, neg_apply, hu p, neg_one_smul]
    rw [he]
  · intro z
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change g.inner z.1.1 (z.2.1 • V z.1.1) (V z.1.1) = z.2.1
      simp only [map_smul, smul_apply, smul_eq_mul, hunit _ z.1.2, mul_one]
  · have hp : Continuous (fun p : P => unitRicciKernelProjection D p.1) :=
      (continuous_unitRicciKernelProjection D).comp continuous_subtype_val
    have hs : Continuous (fun p : P => (V p.1.1.proj : TangentBundle (𝓡 n) M)) :=
      hV.continuousOn.comp_continuous hp (fun p => p.2)
    have hqcont : Continuous q :=
      (continuous_subtype_val.comp continuous_subtype_val).inner_bundle hs
    exact (hp.subtype_mk _).prodMk (hqcont.subtype_mk _)
  · apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_prod_of_discrete_right.mpr
    intro s
    exact (hV.const_smul_section (a := s.1)).continuousOn.domRestrict

theorem unitRicciKernel_evenlyCovered_of_terminal_nullity_one
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (hdim : ∀ y : M, ricciNullity (F.connection b) y = 1) (x : M) :
    IsEvenlyCovered (unitRicciKernelProjection (F.connection b)) x LineSign := by
  obtain ⟨U, V, hU, hx, hV, hn⟩ :=
    exists_local_parallel_unit_ricci_null_section hC hab F hsec hdim x
  exact ⟨inferInstance, U, hx, hU,
    hU.preimage (continuous_unitRicciKernelProjection (F.connection b)),
    unitRicciKernelLocalHomeomorph (F.connection b) V hV (fun y _ => hdim y)
      (fun y hy => (hn y hy).1) (fun y hy => (hn y hy).2.1), fun _ => rfl⟩

theorem unitRicciKernel_isCoveringMap_of_terminal_nullity_one
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (hdim : ∀ y : M, ricciNullity (F.connection b) y = 1) :
    IsCoveringMap (unitRicciKernelProjection (F.connection b)) :=
  fun x => (unitRicciKernel_evenlyCovered_of_terminal_nullity_one
    hC hab F hsec hdim x).to_isEvenlyCovered_preimage

theorem unitRicciKernel_fiber_card_of_terminal_nullity_one
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (hdim : ∀ y : M, ricciNullity (F.connection b) y = 1) (x : M) :
    Nat.card (unitRicciKernelProjection (F.connection b) ⁻¹' {x}) = 2 := by
  rw [← Nat.card_congr (unitRicciKernel_evenlyCovered_of_terminal_nullity_one
    hC hab F hsec hdim x).fiberHomeomorph.toEquiv]
  exact Set.ncard_pair (by norm_num : (1 : ℝ) ≠ -1)

def unitRicciKernelReverse (D : LeviCivitaData g) (p : UnitRicciKernel D) : UnitRicciKernel D :=
  ⟨⟨p.1.proj, -p.1.snd⟩, by
    constructor
    · simpa only [map_neg, neg_apply, neg_neg] using p.2.1
    · intro w
      rw [← ricciBilinear_apply, map_neg, LinearMap.neg_apply, ricciBilinear_apply,
        p.2.2 w, neg_zero]⟩

theorem continuous_unitRicciKernelReverse (D : LeviCivitaData g) :
    Continuous (unitRicciKernelReverse D) := by
  apply Continuous.subtype_mk
  rw [continuous_iff_continuousAt]
  intro p
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨(continuous_unitRicciKernelProjection D).continuousAt, ?_⟩
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p.1.proj
  have hc := ((FiberBundle.continuousAt_totalSpace
    (EuclideanSpace ℝ (Fin n)) (fun q : UnitRicciKernel D => q.1) (x₀ := p)).mp
      continuous_subtype_val.continuousAt).2
  apply hc.neg.congr
  have hnear : ∀ᶠ q : UnitRicciKernel D in 𝓝 p, q.1.proj ∈ e.baseSet :=
    (continuous_unitRicciKernelProjection D).continuousAt.eventually
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt _ _ _))
  filter_upwards [hnear] with q hq
  change -(e q.1).2 = (e ⟨q.1.proj, -q.1.snd⟩).2
  rw [← e.continuousLinearMapAt_apply_of_mem (R := ℝ) hq,
    ← e.continuousLinearMapAt_apply_of_mem (R := ℝ) hq, map_neg]

theorem unitRicciKernelReverse_involutive (D : LeviCivitaData g) :
    Function.Involutive (unitRicciKernelReverse D) := by
  intro p
  apply Subtype.ext
  simp only [unitRicciKernelReverse, neg_neg]

def unitRicciKernelDeckHomeomorph (D : LeviCivitaData g) : UnitRicciKernel D ≃ₜ UnitRicciKernel D where
  toFun := unitRicciKernelReverse D
  invFun := unitRicciKernelReverse D
  left_inv := unitRicciKernelReverse_involutive D
  right_inv := unitRicciKernelReverse_involutive D
  continuous_toFun := continuous_unitRicciKernelReverse D
  continuous_invFun := continuous_unitRicciKernelReverse D

theorem unitRicciKernelReverse_fixedPointFree (D : LeviCivitaData g)
    (p : UnitRicciKernel D) : unitRicciKernelReverse D p ≠ p := by
  intro h
  have he : -p.1.snd = p.1.snd := TotalSpace.mk_inj.mp (congrArg Subtype.val h)
  have hv0 : p.1.snd = 0 := by
    have : (2 : ℝ) • p.1.snd = 0 := by
      rw [two_smul]
      nth_rw 1 [← he]
      exact neg_add_cancel _
    exact (smul_eq_zero.mp this).resolve_left (by norm_num)
  have hu := p.2.1
  simp only [hv0, map_zero] at hu
  norm_num at hu

@[simp] theorem unitRicciKernelProjection_reverse (D : LeviCivitaData g)
    (p : UnitRicciKernel D) :
    unitRicciKernelProjection D (unitRicciKernelReverse D p) = unitRicciKernelProjection D p := rfl

end PoincareConjecture.RicciFlow.Splitting

namespace PoincareConjecture.RicciFlow

theorem unitRicciKernel_doubleCover_of_terminal_null_plane
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M (Iic 0))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hnonflat : ∃ p, (F.connection 0).curvatureTensorNorm p ≠ 0)
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (F.metric 0).inner x v v = 1)
    (hw : (F.metric 0).inner x w w = 1)
    (hvw : (F.metric 0).inner x v w = 0)
    (hzero : (F.connection 0).curvatureTensor x v w v w = 0) :
    IsCoveringMap (Splitting.unitRicciKernelProjection (F.connection 0)) ∧
      ∀ p : M, Nat.card (Splitting.unitRicciKernelProjection (F.connection 0) ⁻¹' {p}) = 2 := by
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F
    (show Icc (-1 : ℝ) 0 ⊆ Iic (0 : ℝ) from fun _ hs => hs.2) ordConnected_Icc
    ⟨-1, by norm_num, 0, by norm_num, by norm_num⟩
  have hsec : ∀ s ∈ Icc (-1 : ℝ) 0, (G.connection s).NonnegativeSectionalCurvature := by
    intro s hs q a b
    exact (F.connection s).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      q (hoperator s hs.2 q) a b
  have hdim := F.ricciNullity_eq_one_of_terminal_null_plane hC hoperator hnonflat
    x v w hv hw hvw hzero
  exact ⟨Splitting.unitRicciKernel_isCoveringMap_of_terminal_nullity_one hC (by norm_num)
    G hsec hdim, Splitting.unitRicciKernel_fiber_card_of_terminal_nullity_one hC (by norm_num)
      G hsec hdim⟩

end PoincareConjecture.RicciFlow
