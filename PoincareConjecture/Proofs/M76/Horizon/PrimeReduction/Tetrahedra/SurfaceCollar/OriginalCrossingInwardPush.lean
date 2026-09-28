import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalChartInwardPush
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.ConvexFrontierSides

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_crossing_inward_push
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (B : OpenPartialHomeomorph X V3)
    (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3)
    {R S O : Set X} (hR : IsClosed R) (hreg : closure (interior R) = R)
    (hO : IsOpen O) {y : X} (hyB : y ∈ B.source) (hBy : B y = 0)
    (hyO : y ∈ O)
    (hfront : ∀ x ∈ B.source, x ∈ frontier R ↔ B x 0 = 0)
    (hS : ∀ x ∈ B.source, x ∈ S ↔ B x 1 = 0) :
    ∃ H : X ≃ₜ X,
      (∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (H.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      EqOn H id Oᶜ ∧ (∀ x, H x ∈ S ↔ x ∈ S) ∧
      (∀ x ∈ R, H x ∈ interior R ∨ H x = x) ∧ H y ∈ interior R := by
  have hyF : y ∈ frontier R := (hfront y hyB).mpr (by rw [hBy]; rfl)
  obtain ⟨r,hr,hrT⟩ := Metric.isOpen_iff.mp B.open_target 0
    (hBy ▸ B.map_source hyB)
  let D := (B.symm.restrOpen (ball 0 r) isOpen_ball).symm
  have hDsource : D.source ⊆ B.source := inter_subset_left
  have hDtarget : D.target = ball 0 r := inter_eq_right.mpr hrT
  have hyD : y ∈ D.source := ⟨hyB,by change B y ∈ ball 0 r; rw [hBy]; exact mem_ball_self hr⟩
  have hD (i : ι) : (e i).symm.trans D ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact (hB i).1.mono ((e i).symm.trans D).open_source
      (fun _ hx => ⟨hx.1,hDsource hx.2⟩)
  let ell : V3 →L[ℝ] ℝ := ContinuousLinearMap.proj (0 : Fin 3)
  let A : V3 →ᵃ[ℝ] ℝ := (ContinuousLinearMap.proj (1 : Fin 3)).toLinearMap.toAffineMap
  have hDfront (x : X) (hx : x ∈ D.source) : x ∈ frontier R ↔ ell (D x) = 0 :=
    hfront x (hDsource hx)
  have hplane (z : V3) (hz : z ∈ D.target) : D.symm z ∈ S ↔ A z = 0 := by
    have hp := hS (D.symm z) (hDsource (D.map_target hz))
    change (D.symm z ∈ S ↔ (D (D.symm z)) 1 = 0) at hp
    rw [D.right_inv hz] at hp
    exact hp
  have hAy : A (D y) = 0 := by change B y 1 = 0; rw [hBy]; rfl
  have hside := halfspace_of_convex_linear_frontier_chart hR hreg hyF D hyD ell
    (hDtarget ▸ convex_ball 0 r) hDfront
  rcases hside with hp | hn
  · have hconv : Convex ℝ (ell ⁻¹' Ici 0) := (convex_Ici (0 : ℝ)).linear_preimage ell.toLinearMap
    have hw : (Pi.single 0 1 : V3) ∈ interior (ell ⁻¹' Ici 0) := by
      apply (interior_maximal (fun x hx => le_of_lt hx)
        (isOpen_lt continuous_const ell.continuous))
      change 0 < (Pi.single 0 (1 : ℝ) : V3) 0
      simp
    apply exists_original_chart_inward_push e he D hD hO D.open_target Subset.rfl
      hconv (fun z hz => by simpa only [mem_preimage,mem_Ici,D.right_inv hz] using hp (D.symm z) (D.map_target hz))
      A hplane hyD (D.map_source hyD) (hR.frontier_subset hyF) hyO hw
    rw [hAy]
    simp [A]
  · have hconv : Convex ℝ (ell ⁻¹' Iic 0) := (convex_Iic (0 : ℝ)).linear_preimage ell.toLinearMap
    have hw : (Pi.single 0 (-1) : V3) ∈ interior (ell ⁻¹' Iic 0) := by
      apply (interior_maximal (fun x hx => le_of_lt hx)
        (isOpen_lt ell.continuous continuous_const))
      change (Pi.single 0 (-1 : ℝ) : V3) 0 < 0
      simp
    apply exists_original_chart_inward_push e he D hD hO D.open_target Subset.rfl
      hconv (fun z hz => by simpa only [mem_preimage,mem_Iic,D.right_inv hz] using hn (D.symm z) (D.map_target hz))
      A hplane hyD (D.map_source hyD) (hR.frontier_subset hyF) hyO hw
    rw [hAy]
    simp [A]

end PoincareConjecture.M76
