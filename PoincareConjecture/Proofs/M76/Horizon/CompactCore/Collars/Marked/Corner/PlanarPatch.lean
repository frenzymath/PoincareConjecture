import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Marked.Corner.FrontierPatch
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Marked.Corner.PhysicalLift
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Marked.Corner.NormalizedLift



set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

open Dehn.Annuli.RimBands

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem OriginalDiskProduct.exists_corner_planar_patch
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R S T D : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹'
      (P.map '' (Disk ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))))
    (hD : j '' Disk ⊆ D) {y : X} (B : OriginalSurfacePairChart e D T y true)
    (σ : ℝ)
    (hS : ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ S ↔ (B.coordinates z).1.2 = 0)
    (hfront : ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔
      ((B.coordinates z).1.2 = 0 ∧ 0 ≤ σ * (B.coordinates z).1.1) ∨
      ((B.coordinates z).1.1 = 0 ∧ 0 ≤ (B.coordinates z).1.2))
    (H : Rim ≃ₜ Rim) (hH : H.IsFinitePL) (h : V2 → V2)
    (hh : ∀ z : Rim, (H z : V2) = h z)
    (side : Bool) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    {p : ℝ → X} (hp : PolyhedralPLInCharts e p (Icc a b)) (hpi : InjOn p (Icc a b))
    (hps : MapsTo p (Icc a b) B.chart.source)
    (hpc : MapsTo (B.chart ∘ p) (Icc a b) B.coordinates.source)
    (hcenter : ∀ s ∈ Icc a b, p s = j (h (armPoint side s))) :
    ∃ (w : ℝ) (g : P2 → P2), 0 < w ∧ w ≤ 1 / 2 ∧
      FinitePiecewiseAffineOn g (Icc (-w) w ×ˢ Icc a b) ∧
      InjOn g (Icc (-w) w ×ˢ Icc a b) ∧
      MapsTo g (Icc (-w) w ×ˢ Icc a b)
        (Ioo (-(1 / 2 : ℝ)) (3 / 2) ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)) ∧
      (∀ s ∈ Icc a b, g (0, s) = (s, 0)) ∧
      (∀ z ∈ Icc (-w) w ×ˢ Icc a b, (g z).2 = 0 ↔ z.1 = 0) ∧
      ∀ z ∈ Icc (-w) w ×ˢ Icc a b,
        (P.map (h (armPoint side (g z).1), (g z).2) ∈ S ↔ p z.2 ∈ S) ∧
        (P.map (h (armPoint side (g z).1), (g z).2) ∈ T ↔ p z.2 ∈ T) := by
  have harm (s) (hs : s ∈ Icc a b) : armPoint side s ∈ Rim :=
    (armPoint_mem side ⟨by linarith [hs.1], by linarith [hs.2]⟩).1
  have hc (s) (hs : s ∈ Icc a b) : h (armPoint side s) ∈ Rim :=
    hh ⟨_, harm s hs⟩ ▸ (H ⟨_, harm s hs⟩).property
  have hpD : MapsTo p (Icc a b) (j '' Disk) := by
    intro s hs
    exact ⟨_, sphere_subset_closedBall (hc s hs), (hcenter s hs).symm⟩
  have hpf : MapsTo p (Icc a b) (frontier R) := by
    intro s hs
    rw [hcenter s hs, ← P.central _ (sphere_subset_closedBall (hc s hs))]
    exact (P.proper _ ⟨sphere_subset_closedBall (hc s hs), by norm_num⟩).mpr (hc s hs)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := isFinitePLBallPair_Icc hab
  obtain ⟨F, hF, hFi, hFf, hF0, hFzero, hFmark⟩ := B.exists_corner_frontier_patch hD
    he.cover σ hS hfront K hK (hKs.symm ▸ hp) (hKs.symm ▸ hpi)
    (hKs.symm ▸ hps) (hKs.symm ▸ hpc) (hKs.symm ▸ hpD) (hKs.symm ▸ hpf)
  let F' : P2 → X := fun z => F (z.2, z.1)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨L, hL, hLs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)).prod (isFinitePLBallPair_Icc hab)
  let swap : P2 →ᴬ[ℝ] P2 := (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearMap.toContinuousAffineMap
  have hswap : MapsTo swap (I ×ˢ Icc a b) (K.space ×ˢ I) :=
    fun z hz => ⟨hKs.symm.subset hz.2, hz.1⟩
  have hF' : PolyhedralPLInCharts e F' (I ×ˢ Icc a b) :=
    hLs ▸ hF.comp_finitePiecewiseAffineOn L hL
      ⟨L, hL, rfl, L.affineOnFaces_affine swap⟩ (fun z hz => hswap (hLs.subset hz))
  obtain ⟨v, q, hv, hvsmall, hq, hqi, hqmap, hq0, hqF, hqzero⟩ :=
    P.exists_local_band_lift he hopen hab hF'
      (fun z hz u hu hzu => Prod.swap_injective (hFi (hswap hz) (hswap hu) hzu))
      (fun z hz => hFf (hswap hz)) (fun s => h (armPoint side s)) hc
      (fun s hs => (hF0 s (hKs.symm.subset hs)).trans (hcenter s hs))
      (fun z hz => hFzero (z.2, z.1) (hswap hz))
  obtain ⟨q', hq', hq'i, hq'map, hq'eq⟩ := exists_normalized_rim_lift H hH hq hqi hqmap
  have hq'0 (s) (hs : s ∈ Icc a b) : q' (0, s) = (armPoint side s, 0) := by
    have hmem : (0, s) ∈ Icc (-v) v ×ˢ Icc a b := ⟨⟨by linarith, hv.le⟩, hs⟩
    rw [hq'eq _ hmem]
    have heq : (⟨(q (0, s)).1, (hqmap hmem).1⟩ : Rim) = H ⟨_, harm s hs⟩ := by
      apply Subtype.ext
      change (q (0, s)).1 = (H ⟨armPoint side s, harm s hs⟩ : V2)
      rw [hq0 s hs, hh]
    rw [heq, H.symm_apply_apply, hq0 s hs]
  have hq'z (z) (hz : z ∈ Icc (-v) v ×ˢ Icc a b) : (q' z).2 = 0 ↔ z.1 = 0 := by
    rw [hq'eq z hz]
    exact hqzero z hz
  obtain ⟨w, g, hw, hwv, hwsmall, hg, hgi, hgmap, hg0, hgq, hgz⟩ :=
    exists_partial_planar_coordinates ha hab hb hv hvsmall side hq' hq'i hq'map hq'0 hq'z
  have hsub : Icc (-w) w ×ˢ Icc a b ⊆ Icc (-v) v ×ˢ Icc a b := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  refine ⟨w, g, hw, hwsmall, hg, hgi, hgmap, hg0, hgz, ?_⟩
  intro z hz
  have heq : (h (armPoint side (g z).1), (g z).2) = q z := by
    have hback := hgq z hz
    rw [hq'eq z (hsub hz)] at hback
    have heq1 := congrArg Prod.fst hback
    have heq2 := congrArg Prod.snd hback
    dsimp only at heq1 heq2
    apply Prod.ext
    · change h (armPoint side (g z).1) = (q z).1
      rw [heq1, ← hh (H.symm ⟨_, (hqmap (hsub hz)).1⟩), H.apply_symm_apply]
    · exact heq2
  rw [heq, hqF z (hsub hz)]
  exact hFmark (z.2, z.1)
    ⟨hKs.symm.subset hz.2, ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩⟩

end PoincareConjecture.M76
