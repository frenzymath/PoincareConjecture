import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M25

attribute [local instance] SphereBundleCircleModel.carrier_topology
  SphereBundleCircleModel.carrier_charted SphereBundleCircleModel.carrier_manifold

theorem exists_circle_certificate_on_compact_open_component
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    {g : RiemannianMetric 3 M} {X : Set M}
    (W : TopologicalSpace.Opens M)
    (hconnected : IsConnected (W : Set M))
    (hcompact : IsCompact (W : Set M)) (hX : X ⊆ (W : Set M))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_cap : epsilon ≤ 1 / 200)
    (p : W → UnitCircle) (hp : Continuous p) (hsurj : Function.Surjective p)
    (hpsmooth : ContMDiff (𝓡 3) (𝓡 1) ∞ p)
    (hcharts : ∀ b : UnitCircle, ∃ V : Set UnitCircle, IsOpen V ∧ b ∈ V ∧
      ∃ T : OpenPartialHomeomorph W (UnitTwoSphere × UnitCircle),
        T.source = p ⁻¹' V ∧ T.target = univ ×ˢ V ∧
        ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞ T T.source ∧
        ContMDiffOn ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ T.symm T.target ∧
        ∀ x ∈ T.source, (T x).2 = p x)
    (necks : Set (EpsilonNeck g))
    (hnecks : ∀ N ∈ necks, N.epsilon = epsilon)
    (hcover : (W : Set M) = ⋃ N : {N // N ∈ necks}, N.1.carrier)
    (hisotopy : ∀ N ∈ necks, ∃ b : UnitCircle,
      SmoothSphereIsotopicIn (W : Set M) N.central_sphere
        ((Subtype.val : W → M) '' (p ⁻¹' {b}))) :
    ∃ F : SphereBundleCircleCertificate g X,
      F.carrier = (W : Set M) ∧ F.epsilon = epsilon := by
  classical
  obtain ⟨x₀, hx₀⟩ := hconnected.nonempty
  have hclopen : IsClopen (W : Set M) := ⟨hcompact.isClosed, W.isOpen⟩
  have hcomponent : ∃ x : M, (W : Set M) = connectedComponent x := by
    refine ⟨x₀, ?_⟩
    apply Subset.antisymm
    · exact hconnected.subset_connectedComponent hx₀
    · exact hclopen.connectedComponent_subset hx₀
  let hWne : Nonempty W := ⟨⟨x₀, hx₀⟩⟩
  let forward : M → W := fun x =>
    if hx : x ∈ (W : Set M) then ⟨x, hx⟩ else Classical.choice hWne
  have hforward_on (x : W) : forward x.1 = x := by
    simp only [forward]
    split
    · rename_i hx
      exact Subtype.ext (by rfl)
    · rename_i hx
      exact False.elim (hx x.property)
  have hforward_smooth :
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ forward (W : Set M) := by
    have hcomp : ContMDiffOn (𝓡 3) (𝓡 3) ∞
        (Subtype.val ∘ forward) (W : Set M) := by
      refine contMDiff_id.contMDiffOn.congr ?_
      intro x hx
      change (forward x).1 = x
      exact congrArg Subtype.val (hforward_on ⟨x, hx⟩)
    intro x hx
    exact (ContMDiffWithinAt.subtypeVal_comp_iff W forward (W : Set M) x).mp
      (hcomp x hx)
  let model : SphereBundleCircleModel.{u} := {
    carrier := W
    carrier_topology := inferInstance
    carrier_charted := inferInstance
    carrier_manifold := inferInstance
    projection := p
    projection_continuous := hp
    projection_surjective := hsurj
    projection_smooth := hpsmooth
    local_trivialization := by
      intro b
      obtain ⟨V, hV, hb, T, hTs, hTt, hTsm, hTism, hTp⟩ := hcharts b
      refine ⟨V, hV, hb, T, T.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← hTs, ← hTt]
        exact T.image_source_eq_target
      · rw [← hTs]
        exact T.leftInvOn
      · rw [← hTt]
        exact T.rightInvOn
      · rwa [← hTs]
      · rwa [← hTt]
      · rwa [← hTs] }
  have hfiber (b : UnitCircle) :
      {x : M | x ∈ (W : Set M) ∧ p (forward x) = b} =
        (Subtype.val : W → M) '' (p ⁻¹' {b}) := by
    ext x
    constructor
    · rintro ⟨hx, hpx⟩
      let y : W := ⟨x, hx⟩
      have hfy : forward x = y := hforward_on y
      have hy : y ∈ p ⁻¹' {b} := by
        change p y ∈ ({b} : Set UnitCircle)
        rw [mem_singleton_iff]
        rw [← hfy]
        exact hpx
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      have hpy : p y = b := by
        simpa [mem_singleton_iff] using hy
      refine ⟨y.property, ?_⟩
      rw [hforward_on y]
      exact hpy
  refine ⟨{
    epsilon := epsilon
    epsilon_pos := hepsilon
    epsilon_le_one_two_hundred := hepsilon_cap
    carrier := (W : Set M)
    contains_X := hX
    connected := hconnected
    compact := hcompact
    component := hcomponent
    model := model
    homeomorph := Homeomorph.refl W
    forward := forward
    inverse := Subtype.val
    forward_eq := ?_
    inverse_eq := ?_
    forward_smooth := hforward_smooth
    inverse_smooth := contMDiff_subtype_val
    necks := necks
    neck_epsilon := hnecks
    neck_cover := hcover
    fiber_isotopy := ?_ }, rfl, rfl⟩
  · intro x
    exact hforward_on x
  · intro y
    rfl
  · intro N hN
    obtain ⟨b, hb⟩ := hisotopy N hN
    refine ⟨b, ?_⟩
    rw [hfiber b]
    simpa [model] using hb

end PoincareConjecture.M25
