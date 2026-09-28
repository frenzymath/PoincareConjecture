import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.FrontierBlockOpenCover
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.DiskBlockFrontierRetraction
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Topology.HomotopyLoopContractions
import PoincareConjecture.Proofs.M76.Horizon.Dependencies.AlgebraicTopology.FundamentalGroup.VanKampen.MapNullhomotopy









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)
local notation "T" => Icc (-1 : ℝ) 1

theorem OriginalDiskProduct.frontier_block_subset
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {K F Y : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e K j) (hFY : F ⊆ Y) (hPY : MapsTo P.map (D ×ˢ T) Y) :
    F ∪ P.closedStrip ⊆ Y := by
  rintro x (hx | ⟨z, hz, rfl⟩)
  · exact hFY hx
  · exact hPY ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩





theorem OriginalDiskProduct.frontier_block_loops_contract
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {K F Y : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e K j) (hF : IsCompact F)
    (hPF : ∀ z ∈ D ×ˢ T, P.map z ∈ F ↔ z.1 ∈ Q)
    (hlateral : IsOpen ((Subtype.val : F → X) ⁻¹'
      (P.map '' (Q ×ˢ Ioo (-(3 / 4 : ℝ)) (3 / 4)))))
    (hFY : F ⊆ Y) (hPY : MapsTo P.map (D ×ˢ T) Y)
    (hFnull : ∀ (x : F) (p : Path x x),
      (p.map (ContinuousMap.inclusion hFY).continuous).Homotopic
        (Path.refl ((ContinuousMap.inclusion hFY) x)))
    (x : (F ∪ P.closedStrip : Set X)) (p : Path x x) :
    (p.map (ContinuousMap.inclusion (P.frontier_block_subset hFY hPY)).continuous).Homotopic
      (Path.refl ((ContinuousMap.inclusion (P.frontier_block_subset hFY hPY)) x)) := by
  let Z := F ∪ P.closedStrip
  let core := P.map '' (closedBall (0 : V2) (1 / 2) ×ˢ J)
  let band := P.map '' (Q ×ˢ Ioo (-(3 / 4 : ℝ)) (3 / 4))
  let U : Set Z := (Subtype.val : Z → X) ⁻¹' coreᶜ
  let V : Set Z := (Subtype.val : Z → X) ⁻¹' (P.closedStrip ∪ band)
  let Us := Z \ core
  let f : C(Z, Y) := ContinuousMap.inclusion (P.frontier_block_subset hFY hPY)
  obtain ⟨hU, hV, hcover, _, _⟩ := P.frontier_block_open_cover hF hPF hlateral
  have htop : ContractibleSpace V ∧ IsPathConnected (U ∩ V) := by
    have hc : P.map '' DiskBlockCover.cover = P.closedStrip ∪ band := by
      simp only [DiskBlockCover.cover, DiskBlockCover.block, DiskBlockCover.lateral,
        image_union, neg_div, OriginalDiskProduct.closedStrip, band]
    have hcore : P.map '' DiskBlockCover.core = core := by
      simp only [DiskBlockCover.core, core, neg_div]
    have ht := P.frontier_block_cover_topology hPF
    dsimp only at ht
    rw [hc, hcore] at ht
    exact ht
  letI : ContractibleSpace V := htop.1
  have hVp : IsPathConnected V := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  obtain ⟨r, H, _, _⟩ := exists_disk_block_frontier_retraction P F hF hPF
  let HY := (ContinuousMap.Homotopy.refl f).comp H
  have hUnull (a : Z) (q : Path a a) (hq : ∀ t, q t ∈ U) :
      (q.map f.continuous).Homotopic (Path.refl (f a)) := by
    have ha : (a : X) ∉ core := by simpa only [Path.source, U, mem_preimage, mem_compl_iff] using hq 0
    let aU : Us := ⟨a, a.property, ha⟩
    let qU : Path aU aU := {
      toFun := fun t => ⟨q t, (q t).property, hq t⟩
      continuous_toFun := (continuous_subtype_val.comp q.continuous).subtype_mk _
      source' := Subtype.ext (congrArg (fun z : Z => (z : X)) q.source)
      target' := Subtype.ext (congrArg (fun z : Z => (z : X)) q.target) }
    have hlast := hFnull (r aU) (qU.map r.continuous)
    have hlast' : (qU.map (f.comp
        ((ContinuousMap.inclusion (subset_union_left : F ⊆ Z)).comp r)).continuous).Homotopic
        (Path.refl ((f.comp
          ((ContinuousMap.inclusion (subset_union_left : F ⊆ Z)).comp r)) aU)) := by
      exact hlast
    have h := HY.map_loop_homotopic_refl qU hlast'
    exact h
  have hVnull (a : Z) (q : Path a a) (hq : ∀ t, q t ∈ V) :
      (q.map f.continuous).Homotopic (Path.refl (f a)) := by
    let aV : V := ⟨a, by simpa using hq 0⟩
    let qV : Path aV aV := {
      toFun := fun t => ⟨q t, hq t⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
    have h := SimplyConnectedSpace.paths_homotopic qV (Path.refl aV)
    let incl : C(V, Y) := f.comp ⟨Subtype.val, continuous_subtype_val⟩
    exact h.map incl
  exact VanKampen.map_loops_nullhomotopic_of_open_cover f U V hU hV hcover
    hVp htop.2 hUnull hVnull x p

end PoincareConjecture.M76
