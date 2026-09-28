import PoincareConjecture.Proofs.M76.Wall.Mathlib.FinitePLSphereDiskComplement
import PoincareConjecture.Proofs.M76.Wall.OriginalSphereGraphModel
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization
import PoincareConjecture.Proofs.M76.Mathlib.TriangularRoof
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import Mathlib.Topology.Homotopy.Contractible

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem ChartwisePLSphere.exists_disk_complement_of_graph
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S d q : Set X}
    (s : ChartwisePLSphere e S) (F : X → E) (hFc : Continuous F)
    (hFi : InjOn F S)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hqd : q ⊆ d) (hdS : d ⊆ S) (hout : (S \ d).Nonempty)
    (hd : IsFinitePLBallPair (ℝ × ℝ) (F '' d) (F '' q)) :
    ∃ a : D ≃ₜ (S \ (d \ q) : Set X),
      (∀ x : D, (a x : X) ∈ q ↔ (x : V2) ∈ Q) ∧
      ContractibleSpace (S \ (d \ q) : Set X) ∧
      IsFinitePLBallPair (ℝ × ℝ) (F '' (S \ (d \ q))) (F '' q) := by
  obtain ⟨b, hb, hbval⟩ := s.exists_finitePL_graph_sphere F hFc hFi hF
  let bfront := b.symm.trans (Homeomorph.setCongr
    (frontier_closedBall (0 : V3) one_ne_zero).symm)
  have hbfront : bfront.IsFinitePL := by
    exact hb.symm.setCongr rfl (frontier_closedBall (0 : V3) one_ne_zero).symm
  have houtF : (F '' S \ F '' d).Nonempty := by
    obtain ⟨x, hxS, hxd⟩ := hout
    refine ⟨F x, mem_image_of_mem F hxS, ?_⟩
    rintro ⟨y, hyd, hyx⟩
    exact hxd (hFi (hdS hyd) hxS hyx ▸ hyd)
  have hcomp := hbfront.sphere_disk_complement
    (isCompact_closedBall (0 : V3) 1) (convex_closedBall (0 : V3) 1)
    (by rw [interior_closedBall (0 : V3) one_ne_zero]; exact ⟨0, by simp⟩)
    (by simp) hd (image_mono hdS) houtF
  let T : Set X := S \ (d \ q)
  have himage : F '' T = F '' S \ (F '' d \ F '' q) := by
    change F '' (S \ (d \ q)) = _
    rw [hFi.image_sdiff_subset (sdiff_subset.trans hdS),
      (hFi.mono hdS).image_sdiff_subset hqd]
  have hcompT : IsFinitePLBallPair (ℝ × ℝ) (F '' T) (F '' q) :=
    himage.symm ▸ hcomp
  let j : S ≃ₜ F '' S := s.parametrization.symm.trans b
  have hj (x : S) : (j x : E) = F x := by
    change (b (s.parametrization.symm x) : E) = F x
    rw [hbval, s.map_eq, s.parametrization.apply_symm_apply]
  have hjT (x : S) : (x : X) ∈ T ↔ (j x : E) ∈ F '' T := by
    rw [hj]
    constructor
    · exact mem_image_of_mem F
    · rintro ⟨y, hy, hyx⟩
      exact hFi hy.1 x.property hyx ▸ hy
  let jT : T ≃ₜ F '' T :=
    j.restrictSubsets sdiff_subset (image_mono sdiff_subset) hjT
  have hjTval (x : T) : (jT x : E) = F x := hj ⟨x, x.property.1⟩
  let coordinates : (ℝ × ℝ) ≃L[ℝ] V2 :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  obtain ⟨c, hc, hcb⟩ := hcompT.exists_cube_chart coordinates
  let a : D ≃ₜ T := c.symm.trans jT.symm
  have harim (x : D) : (a x : X) ∈ q ↔ (x : V2) ∈ Q := by
    have hax : (jT (a x) : E) = (c.symm x : E) := by
      change (jT (jT.symm (c.symm x)) : E) = _
      rw [jT.apply_symm_apply]
    have hq : (a x : X) ∈ q ↔ (c.symm x : E) ∈ F '' q := by
      rw [← hax, hjTval]
      constructor
      · exact mem_image_of_mem F
      · rintro ⟨y, hy, hyx⟩
        exact hFi (hdS (hqd hy)) (a x).property.1 hyx ▸ hy
    have hbdy := hcb (c.symm x)
    rw [c.apply_symm_apply, frontier_closedBall (0 : V2) one_ne_zero] at hbdy
    exact hq.trans hbdy
  let : ContractibleSpace D :=
    (convex_closedBall (0 : V2) 1).contractibleSpace ⟨0, by simp⟩
  exact ⟨a, harim, a.symm.contractibleSpace, hcompT⟩

private theorem unit_square_disk_pair : IsFinitePLBallPair (ℝ × ℝ) D Q := by
  let coordinates : (ℝ × ℝ) ≃L[ℝ] V2 :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  obtain ⟨c, hc, hcb⟩ :=
    TriangularRoofModel.isFinitePLBallPair_base.exists_cube_chart coordinates
  apply TriangularRoofModel.isFinitePLBallPair_base.of_homeomorph
    sphere_subset_closedBall c.symm hc.symm
  intro x
  have hb := hcb (c.symm x)
  rw [c.apply_symm_apply, frontier_closedBall (0 : V2) one_ne_zero] at hb
  exact hb.symm

theorem ChartwisePLSphere.exists_disk_complement
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (F : X → E) (hFc : Continuous F)
    (hFi : InjOn F S)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (v : V2 → X) (hv : PolyhedralPLInCharts e v D)
    (hvi : InjOn v D) (hvS : MapsTo v D S) (hout : (S \ v '' D).Nonempty) :
    ∃ a : D ≃ₜ (S \ (v '' D \ v '' Q) : Set X),
      (∀ x : D, (a x : X) ∈ v '' Q ↔ (x : V2) ∈ Q) ∧
      ContractibleSpace (S \ (v '' D \ v '' Q) : Set X) ∧
      IsFinitePLBallPair (ℝ × ℝ) (F '' (S \ (v '' D \ v '' Q))) (F '' (v '' Q)) := by
  have hpair := unit_square_disk_pair
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKD, _⟩, _⟩, _⟩ := hpair
  have hgraph : FinitePiecewiseAffineOn (F ∘ v) D := by
    have hvK : PolyhedralPLInCharts e v K.space := hKD.symm ▸ hv
    exact hKD ▸ hvK.finitePiecewiseAffineOn_comp K hK hF
  have hgraphinj : InjOn (F ∘ v) D := by
    intro x hx y hy hxy
    exact hvi hx hy (hFi (hvS hx) (hvS hy) hxy)
  have hd : IsFinitePLBallPair (ℝ × ℝ) (F '' (v '' D)) (F '' (v '' Q)) := by
    simpa only [image_image, Function.comp_def] using
      unit_square_disk_pair.image hgraph hgraphinj
  exact s.exists_disk_complement_of_graph F hFc hFi hF
    (image_mono sphere_subset_closedBall) (image_subset_iff.mpr hvS) hout hd

end PoincareConjecture.M76
