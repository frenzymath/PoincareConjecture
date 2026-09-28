import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.LocalIsometry.Rigidity
import Mathlib.Topology.Sheaves.LocalPredicate



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace CategoryTheory Opposite
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.SpaceForm

variable {n : ℕ} {M : Type*} {N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]


def isometryPrelocal (g : RiemannianMetric n M) (h : RiemannianMetric n N) :
    TopCat.PrelocalPredicate (fun _ : TopCat.of M => N) where
  pred {U} f := ∃ k : M → N,
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ k U ∧
    (∀ x ∈ U, ∀ v w : TangentSpace (𝓡 n) x,
      g.inner x v w = h.inner (k x)
        (mfderiv (𝓡 n) (𝓡 n) k x v) (mfderiv (𝓡 n) (𝓡 n) k x w)) ∧
    ∀ x : U, k x = f x
  res {U V} i f hf := by
    obtain ⟨k, hk, hm, heq⟩ := hf
    exact ⟨k, hk.mono i.le, fun x hx => hm x (i.le hx),
      fun x => heq ⟨x, i.le x.property⟩⟩



def isometryPredicate (g : RiemannianMetric n M) (h : RiemannianMetric n N) :
    TopCat.LocalPredicate (fun _ : TopCat.of M => N) :=
  (isometryPrelocal g h).sheafify

abbrev isometryPresheaf (g : RiemannianMetric n M) (h : RiemannianMetric n N) :=
  (TopCat.subsheafToTypes (isometryPredicate g h)).presheaf


def sectionExtension [Nonempty N] (U : Opens (TopCat.of M)) (f : U → N) : M → N := by
  classical
  exact fun x => if hx : x ∈ U then f ⟨x, hx⟩ else Classical.choice ‹Nonempty N›

omit [TopologicalSpace N] in
theorem sectionExtension_apply [Nonempty N] (U : Opens (TopCat.of M))
    (f : U → N) {x : M} (hx : x ∈ U) : sectionExtension U f x = f ⟨x, hx⟩ := by
  simp [sectionExtension, hx]



theorem sectionExtension_spec [Nonempty N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    {U : Opens (TopCat.of M)} {f : U → N} (hf : (isometryPredicate g h).pred f) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (sectionExtension U f) U ∧
    ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 n) x,
      g.inner x v w = h.inner (sectionExtension U f x)
        (mfderiv (𝓡 n) (𝓡 n) (sectionExtension U f) x v)
        (mfderiv (𝓡 n) (𝓡 n) (sectionExtension U f) x w) := by
  have hlocal (x : M) (hx : x ∈ U) :
      ∃ k : M → N, (sectionExtension U f) =ᶠ[𝓝 x] k ∧
        ContMDiffAt (𝓡 n) (𝓡 n) ∞ k x ∧
        ∀ v w : TangentSpace (𝓡 n) x, g.inner x v w = h.inner (k x)
          (mfderiv (𝓡 n) (𝓡 n) k x v) (mfderiv (𝓡 n) (𝓡 n) k x w) := by
    obtain ⟨V, hxV, i, k, hk, hm, heq⟩ := hf ⟨x, hx⟩
    refine ⟨k, ?_, hk.contMDiffAt (V.isOpen.mem_nhds hxV), hm x hxV⟩
    filter_upwards [V.isOpen.mem_nhds hxV] with y hy
    rw [sectionExtension_apply U f (i.le hy)]
    exact (heq ⟨y, hy⟩).symm
  constructor
  · intro x hx
    obtain ⟨k, heq, hk, _⟩ := hlocal x hx
    exact (hk.congr_of_eventuallyEq heq).contMDiffWithinAt
  · intro x hx v w
    obtain ⟨k, heq, _, hm⟩ := hlocal x hx
    rw [heq.mfderiv_eq, heq.self_of_nhds]
    exact hm v w

theorem isometryPredicate_of_map
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (U : Opens (TopCat.of M)) (f : M → N)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hm : ∀ x ∈ U, ∀ v w : TangentSpace (𝓡 n) x,
      g.inner x v w = h.inner (f x)
        (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w)) :
    (isometryPredicate g h).pred (fun x : U => f x) :=
  TopCat.PrelocalPredicate.sheafifyOf ⟨f, hf, hm, fun _ => rfl⟩

theorem isometry_germ_eq_of_eventuallyEq [Nonempty N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    {U V : Opens (TopCat.of M)} {x : M} (hxU : x ∈ U) (hxV : x ∈ V)
    (s : (isometryPresheaf g h).obj (op U)) (t : (isometryPresheaf g h).obj (op V))
    (heq : sectionExtension U s.val =ᶠ[𝓝 x] sectionExtension V t.val) :
    (isometryPresheaf g h).germ U x hxU s = (isometryPresheaf g h).germ V x hxV t := by
  obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.mp
    (inter_mem (U.isOpen.mem_nhds hxU) (inter_mem (V.isOpen.mem_nhds hxV) heq))
  let W' : Opens (TopCat.of M) := ⟨W, hWo⟩
  let iU : W' ⟶ U := homOfLE (fun y hy => (hWsub hy).1)
  let iV : W' ⟶ V := homOfLE (fun y hy => (hWsub hy).2.1)
  have hres : (isometryPresheaf g h).map iU.op s = (isometryPresheaf g h).map iV.op t := by
    apply Subtype.ext
    funext y
    have hy := (hWsub y.property).2.2
    change sectionExtension U s.val y = sectionExtension V t.val y at hy
    rw [sectionExtension_apply U s.val (iU.le y.property),
      sectionExtension_apply V t.val (iV.le y.property)] at hy
    exact hy
  rw [← (isometryPresheaf g h).germ_res_apply iU x hxW s,
    ← (isometryPresheaf g h).germ_res_apply iV x hxW t, hres]

theorem isometry_eventuallyEq_of_germ_eq [Nonempty N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    {U V : Opens (TopCat.of M)} {x : M} (hxU : x ∈ U) (hxV : x ∈ V)
    (s : (isometryPresheaf g h).obj (op U)) (t : (isometryPresheaf g h).obj (op V))
    (heq : (isometryPresheaf g h).germ U x hxU s = (isometryPresheaf g h).germ V x hxV t) :
    sectionExtension U s.val =ᶠ[𝓝 x] sectionExtension V t.val := by
  obtain ⟨W, hxW, iU, iV, hres⟩ := (isometryPresheaf g h).germ_eq x hxU hxV s t heq
  filter_upwards [W.isOpen.mem_nhds hxW] with y hy
  rw [sectionExtension_apply U s.val (iU.le hy), sectionExtension_apply V t.val (iV.le hy)]
  exact congrArg (fun a : (isometryPresheaf g h).obj (op W) => a.val ⟨y, hy⟩) hres


theorem isometry_germ_injective [T2Space M] [CompactSpace M] [T2Space N] [Nonempty N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (U : Opens (TopCat.of M)) (hUc : IsPreconnected (U : Set M))
    (x : M) (hx : x ∈ U) : Function.Injective ((isometryPresheaf g h).germ U x hx) := by
  intro s t hst
  have heq := isometry_eventuallyEq_of_germ_eq g h hx hx s t hst
  obtain ⟨hs, hsm⟩ := sectionExtension_spec g h s.property
  obtain ⟨ht, htm⟩ := sectionExtension_spec g h t.property
  have hglobal := local_isometry_eqOn_of_firstOrder g h U.isOpen hUc hs ht hsm htm hx
    heq.self_of_nhds heq.mfderiv_eq
  apply Subtype.ext
  funext y
  have h := hglobal y.property
  simpa only [sectionExtension_apply U s.val y.property,
    sectionExtension_apply U t.val y.property] using h

end PoincareConjecture.SpaceForm
