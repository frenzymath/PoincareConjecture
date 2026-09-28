import PoincareConjecture.Proofs.M76.Horizon.Dehn.Collars.StandardBoundaryCollar
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Collars.InwardCompression











set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1



theorem exists_standard_inward_compression
    {R : Set V3} (hR : IsCompact R) (hRne : R.Nonempty)
    (he : PLDomain (fun _ : Unit ↦ (Homeomorph.refl V3).toOpenPartialHomeomorph) R) :
    ∃ (s : Finset R) (L : SimplicialComplex ℝ (s → ℝ × V3))
      (HB : L.space ≃ₜ frontier R) (c : (s → ℝ × V3) × ℝ → V3)
      (D : Set V3) (H : R ≃ₜ D),
      L.faces.Finite ∧ HB.IsFinitePL ∧
      FinitePiecewiseAffineOn c (L.space ×ˢ I) ∧ InjOn c (L.space ×ˢ I) ∧
      MapsTo c (L.space ×ˢ I) R ∧
      (∀ x : L.space, c ((x : s → ℝ × V3), 0) = HB x) ∧
      (∀ z ∈ L.space ×ˢ I, c z ∈ frontier R ↔ z.2 = 0) ∧
      H.IsFinitePL ∧ D ⊆ interior R ∧
      (∀ x : L.space,
        (H ⟨HB x, he.closed.frontier_subset (HB x).property⟩ : V3) =
          c ((x : s → ℝ × V3), 1 / 2)) ∧
      ∀ z ∈ L.space ×ˢ I, c z ∈ D ↔ (1 / 2 : ℝ) ≤ z.2 := by
  obtain ⟨K, s, L, HB, c, hK, hKs, hL, hc, hi, hinside, hbase, hfront, hopen⟩ :=
    exists_standard_finite_boundary_collar hR hRne he
  let E := s → ℝ × V3
  let z : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 0)
  have hz : FinitePiecewiseAffineOn z L.space :=
    (L.affineOnFaces_affine z).finitePiecewiseAffineOn hL
  have hzero : FinitePiecewiseAffineOn (fun x : E ↦ c (x, 0)) L.space :=
    hc.comp hz (fun _ hx ↦ ⟨hx, le_rfl, zero_le_one⟩)
  have hHB : HB.IsFinitePL := ⟨_, hzero, fun x ↦ (hbase x).symm⟩
  have hinsideK : MapsTo c (L.space ×ˢ I) K.space :=
    fun _ hz ↦ hKs.symm ▸ hinside hz
  have hopenK : IsOpen ((Subtype.val : K.space → V3) ⁻¹'
      (c '' (L.space ×ˢ Ico (0 : ℝ) 1))) := by
    exact hopen.preimage (Homeomorph.setCongr hKs).continuous
  obtain ⟨D, H0, hH0, hDK, hHval, _, hDheight⟩ :=
    exists_inward_collar_compression K L hK hL c hc hi hinsideK hopenK
  let H : R ≃ₜ D := (Homeomorph.setCongr hKs.symm).trans H0
  have hH : H.IsFinitePL := hH0.setCongr hKs rfl
  have hDR : D ⊆ R := hDK.trans hKs.subset
  have hDint : D ⊆ interior R := by
    intro y hy
    apply (mem_interior_iff_notMem_frontier (hDR hy)).mpr
    intro hyfront
    obtain ⟨x, hx⟩ := HB.surjective ⟨y, hyfront⟩
    have hcy : c ((x : E), 0) = y := (hbase x).trans (congrArg Subtype.val hx)
    have hfalse := (hDheight ((x : E), 0) ⟨x.property, le_rfl, zero_le_one⟩).mp
      (hcy.symm ▸ hy)
    norm_num at hfalse
  refine ⟨s, L, HB, c, D, H, hL, hHB, hc, hi, hinside, hbase, hfront,
    hH, hDint, ?_, hDheight⟩
  intro x
  have h := hHval ((x : E), 0) ⟨x.property, le_rfl, zero_le_one⟩
  have hpoint : (⟨c ((x : E), 0), hinsideK ⟨x.property, le_rfl, zero_le_one⟩⟩ : K.space) =
      (Homeomorph.setCongr hKs.symm)
        ⟨HB x, he.closed.frontier_subset (HB x).property⟩ := Subtype.ext (hbase x)
  rw [hpoint] at h
  simpa only [zero_add, H, Homeomorph.trans_apply] using h

end PoincareConjecture.M76.Dehn
