import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.CompactSphereDiskChart
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.SeparatedCircleSphereAssembly

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

theorem ChartwisePLSphere.exists_flattened_disk_model
    {X E ι : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R T S : Set X}
    (s : ChartwisePLSphere e T) (hR : IsCompact R) (he : PLDomain e R)
    (hTR : T ⊆ interior R) {d r : Set E}
    (hd : IsFinitePLBallPair P2 d r) (p : E → X)
    (hp : PolyhedralPLInCharts e p d) (hpi : InjOn p d)
    (hpT : p '' d ⊆ T) (hcontact : p '' d ∩ S = p '' r)
    (pole : X) (hpoleT : pole ∈ T) (hpole : pole ∉ p '' d) :
    ∃ (Q : OpenPartialHomeomorph X V3) (n : ℕ) (L : Polygon V3 (n + 3)),
      p '' d ⊆ Q.source ∧ Q.source ⊆ interior R ∧
      (∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (∀ x ∈ Q.source, x ∈ T ↔ Q x 2 = 0) ∧
      FinitePiecewiseAffineOn (Q ∘ p) d ∧ InjOn (Q ∘ p) d ∧
      Function.Injective L ∧ L.HasSimplicialEdges ∧
      IsFinitePLBallPair P2 ((Q ∘ p) '' d) (L.boundary ℝ) ∧
      L.boundary ℝ = (Q ∘ p) '' r ∧
      (Q ∘ p) '' d ⊆ Q.target ∩ {x | x 2 = 0} ∧
      ((Q ∘ p) '' d) ∩ Q '' (S ∩ Q.source) = L.boundary ℝ ∧
      Q.symm '' ((Q ∘ p) '' d) = p '' d ∧
      Q.symm '' L.boundary ℝ = p '' r ∧ Q.target = ball (0 : V3) 1 := by
  obtain ⟨Q, hpQ, hQR, hQ, hQT, hQtarget⟩ := s.exists_compact_flattening_chart_with_target hR he hTR
    (hd.isCompact.image_of_continuousOn hp.continuousOn) hpT pole hpoleT hpole
  obtain ⟨K, _, hK, hKd, _, _⟩ := hd.exists_finite_carrier_and_rim_complexes
  have hQp : FinitePiecewiseAffineOn (Q ∘ p) d := by
    rw [← hKd]
    exact (hKd.symm ▸ hp).finitePiecewiseAffineOn_compatible_chart_finite_source K hK Q hQ
      (fun x hx => hpQ ⟨x, hKd.subset hx, rfl⟩)
  have hQpi : InjOn (Q ∘ p) d := by
    intro x hx y hy hxy
    exact hpi hx hy (Q.injOn (hpQ ⟨x, hx, rfl⟩) (hpQ ⟨y, hy, rfl⟩) hxy)
  have hD := hd.image hQp hQpi
  obtain ⟨n, L, hLi, hL, hLr⟩ := hD.exists_polygon_boundary
  have hback (A : Set E) (hAd : A ⊆ d) : Q.symm '' ((Q ∘ p) '' A) = p '' A := by
    rw [image_image]
    exact (image_congr (fun x hx => Q.left_inv (hpQ ⟨x, hAd hx, rfl⟩)))
  refine ⟨Q, n, L, hpQ, hQR, hQ, hQT, hQp, hQpi, hLi, hL,
    hLr.symm ▸ hD, hLr, ?_, ?_, hback d subset_rfl, ?_, hQtarget⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨Q.map_source (hpQ ⟨x, hx, rfl⟩),
      (hQT (p x) (hpQ ⟨x, hx, rfl⟩)).mp (hpT ⟨x, hx, rfl⟩)⟩
  · rw [hLr]
    apply Subset.antisymm
    · rintro _ ⟨⟨x, hx, rfl⟩, y, ⟨hyS, hyQ⟩, hyx⟩
      have hy : y = p x := Q.injOn hyQ (hpQ ⟨x, hx, rfl⟩) hyx
      obtain ⟨z, hz, hzx⟩ := hcontact.subset ⟨⟨x, hx, rfl⟩, hy ▸ hyS⟩
      exact ⟨z, hz, congrArg Q hzx⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hxS : p x ∈ S := (hcontact.symm.subset ⟨x, hx, rfl⟩).2
      exact ⟨⟨x, hd.1 hx, rfl⟩, p x, ⟨hxS, hpQ ⟨x, hd.1 hx, rfl⟩⟩, rfl⟩
  · rw [hLr]
    exact hback r hd.1

end PoincareConjecture.M76
