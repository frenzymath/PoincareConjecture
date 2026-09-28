import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Transport.RetainedDiskProduct



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => Metric.closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1

namespace RelativeFrontierDiskProduct
variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {D W O K : Set X}
  {j : V2 → X} {s : Finset (D ∪ K : Set X)}
  (P : RelativeFrontierDiskProduct e D W O j K s)

include P

theorem base_surface (z : V2) (hz : z ∈ Disk) : j z ∈ frontier D ∩ W := by
  have hzero : (z,(0 : ℝ)) ∈ Disk ×ˢ J := ⟨hz,by norm_num⟩
  have hfront := (P.map_frontier (z,0) hzero).mpr rfl
  have hinside := (P.map_inside hzero).1.1.2
  rw [P.map_central z hz] at hfront hinside
  exact ⟨hfront,hinside⟩

theorem surface_carrier {x : X} (hx : x ∈ frontier D ∩ W) : x ∈ P.carrier :=
  interior_subset (P.neighborhood_subset (P.surface_in_neighborhood hx)).1

theorem product_mem_ambient {z : (s → ℝ × V3) × ℝ}
    (hz : z ∈ (P.stars.marked 2).space ×ˢ I) : P.product z ∈ P.stars.ambient.space := by
  obtain ⟨p,hp⟩ := mem_iUnion.mp (P.product_image.subset ⟨z,hz,rfl⟩)
  exact P.stars.star_subset_ambient p
    (P.stars.dualRegion_subset_star p (Finset.mem_singleton_self _) hp)

theorem physical_product_inverse {x : X} (hx : x ∈ frontier D ∩ W)
    {t : ℝ} (ht : t ∈ I) :
    P.productInverse (P.graph (P.inverse (P.product (P.graph x,t)))) = (P.graph x,t) := by
  have hz : (P.graph x,t) ∈ (P.stars.marked 2).space ×ˢ I :=
    ⟨P.surface_image.symm.subset ⟨x,hx,rfl⟩,ht⟩
  rw [P.graph_inverse _ (P.product_mem_ambient hz)]
  exact P.productInverse_left _ hz



theorem physical_product_mem_cap_iff {x : X} (hx : x ∈ frontier D ∩ W)
    {t : ℝ} (ht : t ∈ I) :
    (P.inverse (P.product (P.graph x,t)) : X) ∈ P.map '' (Disk ×ˢ J) ↔
      x ∈ j '' Disk ∧ t ∈ Icc 0 P.delta := by
  constructor
  · rintro ⟨z,hz,heq⟩
    have hc := congrArg (fun y : X => P.productInverse (P.graph y)) heq
    rw [P.map_productInverse z hz,P.physical_product_inverse hx ht] at hc
    have hxj : j z.1 = x := by
      have hgraph := congrArg Prod.fst hc
      have hinv := congrArg (fun a => (P.inverse a : X)) hgraph
      rw [P.inverse_graph _ (P.surface_carrier (P.base_surface z.1 hz.1)),
        P.inverse_graph _ (P.surface_carrier hx)] at hinv
      exact hinv
    have htime := congrArg Prod.snd hc
    exact ⟨⟨z.1,hz.1,hxj⟩,by
      change 0 ≤ t ∧ t ≤ P.delta
      constructor <;> nlinarith [P.delta_pos,hz.2.1,hz.2.2]⟩
  · rintro ⟨⟨z,hz,rfl⟩,htd⟩
    have htdiv : t / P.delta ∈ J :=
      ⟨div_nonneg htd.1 P.delta_pos.le,(div_le_one P.delta_pos).mpr htd.2⟩
    refine ⟨(z,t/P.delta),⟨hz,htdiv⟩,?_⟩
    rw [P.map_eq]
    simp only [mul_div_cancel₀ t P.delta_pos.ne']

end RelativeFrontierDiskProduct
end PoincareConjecture.M76
