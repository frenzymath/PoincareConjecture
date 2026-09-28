import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.Mathlib.DisjointUnionBicollar
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.InstalledSecondSlabs









set_option autoImplicit false
open Set Geometry Topology Poincare.Topology

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_disjoint_boundary_bicollar
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (phi : C(H0, H0)) {R : Set X0}
    {K0 : Set E} {K1 : Set F} (hK0 : IsCompact K0) (hK1 : IsCompact K1)
    (hne : K0.Nonempty ∨ K1.Nonempty) {r : ℝ} (hr : 0 < r)
    (c0 : E × ℝ → X0) (c1 : F × ℝ → X0)
    (hi0 : IsEmbedding (fun z : (K0 ×ˢ Icc (-r) r : Set (E × ℝ)) => c0 z))
    (hi1 : IsEmbedding (fun z : (K1 ×ˢ Icc (-r) r : Set (F × ℝ)) => c1 z))
    (hdis : Disjoint (c0 '' (K0 ×ˢ Icc (-r) r)) (c1 '' (K1 ×ˢ Icc (-r) r)))
    (ho0 : IsOpen (c0 '' (K0 ×ˢ Ioo (-r) r)))
    (ho1 : IsOpen (c1 '' (K1 ×ˢ Ioo (-r) r)))
    (hzero : (c0 '' (K0 ×ˢ ({0} : Set ℝ))) ∪ (c1 '' (K1 ×ˢ ({0} : Set ℝ))) = frontier R)
    (hside0 : ∀ z ∈ K0 ×ˢ Icc (-r) r, c0 z ∈ R ↔ 0 ≤ z.2)
    (hside1 : ∀ z ∈ K1 ×ˢ Icc (-r) r, c1 z ∈ R ↔ 0 ≤ z.2)
    (g0 : C(K0, C0 × C0)) (hg0 : IsCoveringMap g0)
    (g1 : C(K1, C0 × C0)) (hg1 : IsCoveringMap g1)
    (hproduct0 : ∀ x : K0, ∀ t ∈ Icc (-r) r,
      (Q0 (hamiltonZeroAmbientMap phi (c0 (x, t)))).1 = g0 x)
    (hproduct1 : ∀ x : K1, ∀ t ∈ Icc (-r) r,
      (Q0 (hamiltonZeroAmbientMap phi (c1 (x, t)))).1 = g1 x) :
    let K := Sum.inl '' K0 ∪ Sum.inr '' K1
    let c := sumBicollarMap c0 c1
    ∃ g : C(K, C0 × C0), IsCompact K ∧ K.Nonempty ∧
      ContinuousOn c (K ×ˢ Icc (-r) r) ∧
      IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set ((E ⊕ F) × ℝ)) => c z) ∧
      IsOpen (c '' (K ×ˢ Ioo (-r) r)) ∧
      c '' (K ×ˢ ({0} : Set ℝ)) = frontier R ∧
      (∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ R ↔ 0 ≤ z.2) ∧
      IsCoveringMap g ∧
      ∀ x : K, ∀ t ∈ Icc (-r) r,
        (Q0 (hamiltonZeroAmbientMap phi (c (x, t)))).1 = g x := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let K : Set (E ⊕ F) := Sum.inl '' K0 ∪ Sum.inr '' K1
  let c := sumBicollarMap c0 c1
  have hK : IsCompact K := (hK0.image continuous_inl).union (hK1.image continuous_inr)
  have hKne : K.Nonempty := by
    rcases hne with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact ⟨Sum.inl x, Or.inl ⟨x, hx, rfl⟩⟩
    · exact ⟨Sum.inr x, Or.inr ⟨x, hx, rfl⟩⟩
  have hi : IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set ((E ⊕ F) × ℝ)) => c z) :=
    isEmbedding_sumBicollarMap hK0 hK1 isCompact_Icc c0 c1 hi0 hi1 hdis
  have hz : (0 : ℝ) ∈ Icc (-r) r := ⟨by linarith, hr.le⟩
  have hiK0 : IsEmbedding (fun x : K0 => c0 (x, 0)) :=
    hi0.comp ((Homeomorph.Set.prod K0 (Icc (-r) r)).symm.isEmbedding.comp
      (isEmbedding_prodMkLeft (⟨0, hz⟩ : Icc (-r) r)))
  have hiK1 : IsEmbedding (fun x : K1 => c1 (x, 0)) :=
    hi1.comp ((Homeomorph.Set.prod K1 (Icc (-r) r)).symm.isEmbedding.comp
      (isEmbedding_prodMkLeft (⟨0, hz⟩ : Icc (-r) r)))
  let : T2Space K0 := hiK0.t2Space
  let : T2Space K1 := hiK1.t2Space
  let : CompactSpace K0 := isCompact_iff_compactSpace.mp hK0
  let : CompactSpace K1 := isCompact_iff_compactSpace.mp hK1
  let H : K0 ⊕ K1 ≃ₜ K := sumSubsetHomeomorph K0 K1
  let g : C(K, C0 × C0) :=
    ⟨(Sum.elim g0 g1) ∘ H.symm, (g0.continuous.sumElim g1.continuous).comp H.symm.continuous⟩
  have hg : IsCoveringMap g :=
    (isCoveringMap_sumElim_of_compact hg0 hg1).comp_homeomorph H.symm
  refine ⟨g, hK, hKne, ?_, hi, ?_, ?_, ?_, hg, ?_⟩
  · exact continuousOn_iff_continuous_domRestrict.mpr hi.continuous
  · change IsOpen (sumBicollarMap c0 c1 '' ((Sum.inl '' K0 ∪ Sum.inr '' K1) ×ˢ Ioo (-r) r))
    rw [image_sumBicollarMap]
    exact ho0.union ho1
  · exact (image_sumBicollarMap c0 c1 K0 K1 {0}).trans hzero
  · rintro ⟨z, t⟩ ⟨hz, ht⟩
    rcases hz with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · exact hside0 (x, t) ⟨hx, ht⟩
    · exact hside1 (x, t) ⟨hx, ht⟩
  · intro x t ht
    obtain ⟨w, rfl⟩ := H.surjective x
    change (Q0 (hamiltonZeroAmbientMap phi (c (H w, t)))).1 = Sum.elim g0 g1 (H.symm (H w))
    rw [H.symm_apply_apply]
    cases w with
    | inl x => exact hproduct0 x t ht
    | inr x => exact hproduct1 x t ht

end PoincareConjecture.M76
