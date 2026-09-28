import PoincareConjecture.Proofs.M47.SeedOrdinaryBirthVolume
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometryRicci
import PoincareConjecture.Proofs.M04.PointwiseFlatness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ}

theorem seed_ordinary_ball_subset_image
    (U : TopologicalSpace.Opens C.carrier) [CompactSpace U]
    (e : SurgeryFlowCylinder F C origin scale I U) (s : ℝ) (hs : s ∈ I)
    (g : RiemannianMetric 3 U)
    (hmetric : ∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
      g.inner y v w = (F.metric (origin + s / scale)).inner (e.forward s hs y.val)
        (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y v)
        (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y w))
    (q : U) {R : ℝ} (hR : 0 < R) :
    (F.metric (origin + s / scale)).ball (e.forward s hs q.val) (R / 2) ⊆
      (fun y : U => e.forward s hs y.val) '' g.ball q R := by
  obtain ⟨chart, hsource, hchart⟩ := exists_seed_ordinary_slice_chart U e s hs q
  have hmap : (chart : U → (F.slice (origin + s / scale)).carrier) =
      fun y : U => e.forward s hs y.val := funext hchart
  have hlower : ∀ y ∈ chart.source, ∀ v : TangentSpace (𝓡 3) y,
      g.inner y v v ≤ 4 * (F.metric (origin + s / scale)).inner (chart y)
        (mfderiv (𝓡 3) (𝓡 3) chart y v) (mfderiv (𝓡 3) (𝓡 3) chart y v) := by
    intro y _hy v
    have heq := congrArg (fun f : U → (F.slice (origin + s / scale)).carrier =>
      (F.metric (origin + s / scale)).inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y v) (mfderiv (𝓡 3) (𝓡 3) f y v)) hmap
    rw [heq, ← hmetric]
    have hnonneg : 0 ≤ g.inner y v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact (g.pos y v hv).le
    linarith
  have hcover := seed_ball_subset_image g (F.metric (origin + s / scale)) chart
    hlower q hR isClosed_closure.isCompact (by rw [hsource]; exact subset_univ _)
  simpa only [hmap] using hcover

theorem seed_ordinary_scalar_ball_bound
    (U : TopologicalSpace.Opens C.carrier) [CompactSpace U]
    (e : SurgeryFlowCylinder F C origin scale I U) (s : ℝ) (hs : s ∈ I)
    (g : RiemannianMetric 3 U) (D : LeviCivitaData g)
    (hmetric : ∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
      g.inner y v w = (F.metric (origin + s / scale)).inner (e.forward s hs y.val)
        (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y v)
        (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y w))
    (hread : ∀ y : U, D.scalarCurvature y =
      (F.connection (origin + s / scale)).scalarCurvature (e.forward s hs y.val))
    (q : U) {R K : ℝ} (hR : 0 < R)
    (hscalar : ∀ y ∈ g.ball q R, D.scalarCurvature y ≤ K) :
    ∀ y ∈ (F.metric (origin + s / scale)).ball (e.forward s hs q.val) (R / 2),
      (F.connection (origin + s / scale)).scalarCurvature y ≤ K := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := seed_ordinary_ball_subset_image U e s hs g hmetric q hR hy
  rw [← hread]
  exact hscalar z hz

theorem seed_ordinary_component_ricci_nonnegative
    (U : TopologicalSpace.Opens C.carrier)
    (hcompact : IsCompact (U : Set C.carrier))
    (hconnected : IsConnected (U : Set C.carrier))
    (e : SurgeryFlowCylinder F C origin scale I U) (s : ℝ) (hs : s ∈ I)
    (g : RiemannianMetric 3 U) (D : LeviCivitaData g)
    (hmetric : ∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
      g.inner y v w = (F.metric (origin + s / scale)).inner (e.forward s hs y.val)
        (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y v)
        (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y w))
    (hsec : ∀ y : U, ∀ v w : TangentSpace (𝓡 3) y, 0 ≤ D.curvatureTensor y v w v w)
    (q : U) :
    ∀ y ∈ connectedComponent (e.forward s hs q.val),
      ∀ v : TangentSpace (𝓡 3) y, 0 ≤ (F.connection (origin + s / scale)).ricci y v v := by
  have himage := M47.component_cylinder_image_eq e U.isOpen hcompact hconnected s hs q.property
  intro y hy v
  rw [← himage] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  let zU : U := ⟨z, hz⟩
  let f : U → (F.slice (origin + s / scale)).carrier := fun x => e.forward s hs x.val
  obtain ⟨chart, _hsource, hchart⟩ := exists_seed_ordinary_slice_chart U e s hs q
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f univ := by
    intro x _hx
    have hsource : chart.source = univ := _hsource
    have h := chart.contMDiffOn x (by rw [hsource]; exact mem_univ x)
    simpa only [hsource, show (chart : U → (F.slice (origin + s / scale)).carrier) = f
      from funext hchart] using h
  have hbij := g.mfderiv_bijective_of_pullback_eq (F.metric (origin + s / scale))
    (f := f) zU (fun a b => (hmetric zU a b).symm)
  obtain ⟨w, hw⟩ := hbij.surjective v
  have hRic := D.ricci_eq_of_local_isometry (F.connection (origin + s / scale))
    isOpen_univ hf (fun x _hx => hmetric x) (mem_univ zU) w w
  rw [hw] at hRic
  exact (M04.nonneg_ricci_of_nonnegativeSectionalAt D zU (hsec zU) w).trans_eq hRic

end PoincareConjecture.Proofs.M47
