import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.RegionCompression
import PoincareConjecture.Proofs.M76.Rigidity.OriginalDomainBoundaryCollar
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.PLDomainInteriorConnected








set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_original_common_collar_compression
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hconn : IsConnected R) :
    ∃ (s : Finset R) (K : SimplicialComplex ℝ (s → ℝ × V3))
      (HB : K.space ≃ₜ frontier R) (c : (s → ℝ × V3) × ℝ → X)
      (eps : ℝ) (G : C(R, R)),
      K.faces.Finite ∧ 0 < eps ∧ eps < 1 ∧
      PolyhedralPLInCharts e c (K.space ×ˢ Icc (0 : ℝ) 1) ∧
      IsEmbedding (fun z : (K.space ×ˢ Icc (0 : ℝ) 1) => c z) ∧
      (∀ z, z ∈ K.space ×ˢ Icc (0 : ℝ) 1 → c z ∈ R) ∧
      (∀ x : K.space, c (x, 0) = HB x) ∧
      (∀ z : (K.space ×ˢ Icc (0 : ℝ) 1), c z ∈ frontier R ↔ z.val.2 = 0) ∧
      Function.Injective G ∧ ChartwisePLMap e e G ∧
      range (fun x => (G x : X)) = R \ (c '' (K.space ×ˢ Ico (0 : ℝ) (eps / 2))) ∧
      (∀ z : (K.space ×ˢ Icc (0 : ℝ) eps), ∀ x : R, (x : X) = c z →
        (G x : X) = c (z.val.1, eps / 2 + z.val.2 / 2)) ∧
      (∀ x : R, (x : X) ∉ c '' (K.space ×ˢ Icc (0 : ℝ) eps) → G x = x) ∧
      range (fun x => (G x : X)) ⊆ interior R ∧
      (∀ d, 0 < d → d ≤ eps →
        IsOpen ((Subtype.val : R → X) ⁻¹' (c '' (K.space ×ˢ Ico (0 : ℝ) d)))) := by
  classical
  obtain ⟨s, K, HB, c, hK, hc, hi, hm, hb, hp, delta, hd, hdhalf, _, ho⟩ :=
    he.exists_small_boundary_collar_of_interior_nonempty hR
      (he.isConnected_interior hconn).nonempty isOpen_univ (subset_univ _)
  let eps := delta / 2
  have heps : 0 < eps := half_pos hd
  have hed : eps < delta := half_lt_self hd
  have hd1 : delta ≤ 1 := by linarith
  have hBsub : K.space ×ˢ Icc (0 : ℝ) delta ⊆ K.space ×ˢ Icc (0 : ℝ) 1 :=
    fun z hz => ⟨hz.1, hz.2.1, hz.2.2.trans hd1⟩
  obtain ⟨J, hJ, hJs⟩ := K.exists_finite_interval_product hK hd
  have hcDelta : PolyhedralPLInCharts e c (K.space ×ˢ Icc (0 : ℝ) delta) :=
    hJs ▸ hc.restrict_finite J hJ (hJs.subset.trans hBsub)
  have hfront : frontier R ⊆ c '' (K.space ×ˢ Icc (0 : ℝ) eps) := by
    intro x hx
    obtain ⟨z, hz⟩ := HB.surjective ⟨x, hx⟩
    exact ⟨(z, 0), ⟨z.property, le_rfl, heps.le⟩, (hb z).trans (congrArg Subtype.val hz)⟩
  obtain ⟨x₀, hx₀⟩ := hconn.nonempty
  obtain ⟨G, hGi, hGPL, hGrange, hGval, hGout⟩ :=
    exists_original_common_collar_region_compression e he K hK heps hed c hcDelta
      (hi.comp (IsEmbedding.inclusion hBsub)) (hm.mono_left hBsub)
      (ho eps heps hed.le) (ho delta hd le_rfl) hfront ⟨x₀, hx₀⟩
  refine ⟨s, K, HB, c, eps, G, hK, heps, hed.trans_le hd1, hc, hi, hm, hb, hp,
    hGi, hGPL, hGrange, ?_, hGout, ?_, fun d hd' hde => ho d hd' (hde.trans hed.le)⟩
  · intro z x hx
    have heq : x = (⟨c z, hm ⟨z.property.1, z.property.2.1,
        z.property.2.2.trans (hed.le.trans hd1)⟩⟩ : R) := Subtype.ext hx
    rw [heq]
    exact hGval z
  · intro x hx
    obtain ⟨hxR, hxstrip⟩ := hGrange.subset hx
    apply (mem_interior_iff_notMem_frontier hxR).mpr
    intro hxfront
    obtain ⟨z, hz⟩ := HB.surjective ⟨x, hxfront⟩
    exact hxstrip ⟨(z, 0), ⟨z.property, le_rfl, half_pos heps⟩,
      (hb z).trans (congrArg Subtype.val hz)⟩

end PoincareConjecture.M76
