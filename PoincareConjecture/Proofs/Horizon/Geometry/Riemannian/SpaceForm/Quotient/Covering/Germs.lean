import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Quotient.Covering.Extension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Continuation.Sections
import PoincareConjecture.Proofs.Horizon.Topology.Sheaves.Continuation
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace CategoryTheory Opposite PoincareConjecture PoincareConjecture.SpaceForm
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Geometry.Riemannian.SpaceForm

variable {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [Nonempty M]


theorem locally_bijective_inverse_round_isometry_germ
    (g : RiemannianMetric n M)
    (hsec : ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0 →
        g.leviCivitaData.sectionalCurvature x u v = 1)
    (q : UnitSphere n) :
    ∀ x : UnitSphere n, ∃ U : Opens (TopCat.of (UnitSphere n)), x ∈ U ∧
      ∀ y (hy : y ∈ U),
        Function.Bijective ((isometryPresheaf (roundSphereMetric n) g).germ U y hy) := by
  let : LocallyConnectedSpace (UnitSphere n) :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) _
  obtain ⟨r, hr, hcharts⟩ := exists_uniform_round_chart_radius g hsec q
  intro x
  let U : Opens (TopCat.of (UnitSphere n)) :=
    ⟨connectedComponentIn (Metric.ball x (r / 2)) x, Metric.isOpen_ball.connectedComponentIn⟩
  have hUsub : (U : Set (UnitSphere n)) ⊆ Metric.ball x (r / 2) :=
    connectedComponentIn_subset _ _
  have hxU : x ∈ U := mem_connectedComponentIn (Metric.mem_ball_self (half_pos hr))
  refine ⟨U, hxU, fun y hy => ⟨?_, ?_⟩⟩
  · exact isometry_germ_injective (roundSphereMetric n) g U
      isPreconnected_connectedComponentIn y hy
  · intro a
    obtain ⟨V, hyV, s, hs⟩ := (isometryPresheaf (roundSphereMetric n) g).exists_germ_eq a
    obtain ⟨hks, hkm⟩ := sectionExtension_spec (roundSphereMetric n) g s.property
    let k := sectionExtension V s.val
    obtain ⟨F, hpF, hball, hF, hFi, hFm⟩ := hcharts (k y)
    obtain ⟨f, hf, hfm, hfk⟩ := extend_inverse_round_isometry g V.isOpen hks hkm hyV
      F hpF hF hFi hFm hball
    have hUb : (U : Set (UnitSphere n)) ⊆ Metric.ball y r := by
      intro z hz
      have hz' := hUsub hz
      have hy' := hUsub hy
      rw [Metric.mem_ball] at hz' hy' ⊢
      rw [dist_comm y x] at hy'
      exact (dist_triangle z x y).trans_lt (by linarith)
    let t : (isometryPresheaf (roundSphereMetric n) g).obj (op U) :=
      ⟨fun z => f z, isometryPredicate_of_map (roundSphereMetric n) g U f
        (hf.mono hUb) (fun z hz => hfm z (hUb hz))⟩
    refine ⟨t, (isometry_germ_eq_of_eventuallyEq (roundSphereMetric n) g
      hy hyV t s ?_).trans hs⟩
    have ht : sectionExtension U t.val =ᶠ[𝓝 y] f := by
      filter_upwards [U.isOpen.mem_nhds hy] with z hz
      exact sectionExtension_apply U t.val hz
    exact ht.trans hfk



theorem exists_global_inverse_round_local_isometry
    {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M)
    (hsec : ∀ (x : M) (u v : TangentSpace (𝓡 3) x),
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0 →
        g.leviCivitaData.sectionalCurvature x u v = 1) (p : M) :
    ∃ f : UnitSphere 3 → M, ContMDiff (𝓡 3) (𝓡 3) ∞ f ∧
      ∀ x (v w : TangentSpace (𝓡 3) x),
        (roundSphereMetric 3).inner x v w = g.inner (f x)
          (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) := by
  let : Nonempty M := ⟨p⟩
  let : SimplyConnectedSpace (UnitSphere 3) :=
    Poincare.Topology.sphereSimplyConnected_of_two_le (by norm_num)
  let : LocallyPathConnectedSpace (UnitSphere 3) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
  let q : UnitSphere 3 := ⟨EuclideanSpace.single (0 : Fin 4) (1 : ℝ), by simp⟩
  obtain ⟨F, hp, hFq, hF, hFi, hFm⟩ := exists_local_isometry_unitSphere g hsec p q
  have hq : q ∈ F.target := hFq ▸ F.map_source hp
  let U : Opens (TopCat.of (UnitSphere 3)) := ⟨F.target, F.open_target⟩
  let s : (isometryPresheaf (roundSphereMetric 3) g).obj (op U) :=
    ⟨fun x => F.symm x, isometryPredicate_of_map (roundSphereMetric 3) g U F.symm hFi
      (inverse_local_isometry_inner g (roundSphereMetric 3) F hF hFi hFm)⟩
  obtain ⟨t, _⟩ := Poincare.Topology.exists_globalSection_of_locally_bijective_germ
    (isometryPredicate (roundSphereMetric 3) g)
    (locally_bijective_inverse_round_isometry_germ g hsec q) q
    ((isometryPresheaf (roundSphereMetric 3) g).germ U q hq s)
  obtain ⟨ht, htm⟩ := sectionExtension_spec (roundSphereMetric 3) g t.property
  exact ⟨sectionExtension ⊤ t.val, contMDiffOn_univ.mp ht, fun x => htm x (by trivial)⟩

end Poincare.Geometry.Riemannian.SpaceForm
