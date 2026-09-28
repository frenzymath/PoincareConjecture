import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.PLAtlasTransport
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLDomainMaps










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

variable {X Y X' Y' α β : Type*}
  [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']




theorem ChartwisePLMap.preimage_homeomorph
    {e : α → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {d : β → OpenPartialHomeomorph Y (Fin 3 → ℝ)} {R : Set X} {T : Set Y}
    {f : C(R, T)} (hf : ChartwisePLMap e d f)
    (h : X' ≃ₜ X) (k : Y' ≃ₜ Y)
    (f' : C(h ⁻¹' R, k ⁻¹' T))
    (hmap : ∀ x, k (f' x) = f ⟨h x, x.property⟩) :
    ChartwisePLMap (fun i => h.transOpenPartialHomeomorph (e i))
      (fun j => k.transOpenPartialHomeomorph (d j)) f' := by
  let q : (h ⁻¹' R) ≃ₜ R := h.subtype (fun _ => Iff.rfl)
  refine ⟨hf.source_domain.preimage_homeomorph h,
    hf.target_domain.preimage_homeomorph k, isOpen_univ, ?_⟩
  intro x _
  obtain ⟨i, j, K, V, F, hK, hV, hxV, _, hVe, hVK, hKt, hKU, hF, hcoords⟩ :=
    hf.coordinates (q x) (mem_univ _)
  refine ⟨i, j, K, q ⁻¹' V, F, hK, hV.preimage q.continuous, hxV,
    subset_univ _, ?_, ?_, hKt, ?_, hF, ?_⟩
  · intro y hy
    exact hVe hy
  · rintro z ⟨y, hy, rfl⟩
    exact hVK ⟨q y, hy, rfl⟩
  · intro z hz
    obtain ⟨y, _, hy⟩ := hKU hz
    refine ⟨q.symm y, mem_univ _, ?_⟩
    change h.symm y.val = h.symm ((e i).symm z)
    rw [hy]
  · intro y hy hyK
    obtain ⟨hyj, hFy⟩ := hcoords (q y) hy hyK
    change k (f' y) ∈ (d j).source ∧ F (e i (h y)) = d j (k (f' y))
    rw [hmap]
    exact ⟨hyj, hFy⟩



theorem ChartwisePLHomeomorph.preimage_homeomorph
    {e : α → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {d : β → OpenPartialHomeomorph Y (Fin 3 → ℝ)} {R : Set X} {T : Set Y}
    {f : R ≃ₜ T} (hf : ChartwisePLHomeomorph e d f)
    (h : X' ≃ₜ X) (k : Y' ≃ₜ Y)
    (f' : (h ⁻¹' R) ≃ₜ (k ⁻¹' T))
    (hmap : ∀ x, k (f' x) = f ⟨h x, x.property⟩) :
    ChartwisePLHomeomorph (fun i => h.transOpenPartialHomeomorph (e i))
      (fun j => k.transOpenPartialHomeomorph (d j)) f' := by
  refine ⟨hf.1.preimage_homeomorph h k ⟨f', f'.continuous⟩ hmap,
    hf.2.preimage_homeomorph k h ⟨f'.symm, f'.symm.continuous⟩ ?_⟩
  intro y
  have heq : f ⟨h (f'.symm y), (f'.symm y).property⟩ = ⟨k y, y.property⟩ := by
    apply Subtype.ext
    rw [← hmap, f'.apply_symm_apply]
  have hx : (⟨h (f'.symm y), (f'.symm y).property⟩ : R) =
      f.symm ⟨k y, y.property⟩ :=
    f.injective (heq.trans (f.apply_symm_apply _).symm)
  exact congrArg Subtype.val hx



theorem ChartwisePLMap.transport_homeomorph
    {e : α → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {d : β → OpenPartialHomeomorph Y (Fin 3 → ℝ)}
    {R : Set X} {T : Set Y} {R' : Set X'} {T' : Set Y'}
    {f : C(R, T)} (hf : ChartwisePLMap e d f)
    (h : X' ≃ₜ X) (k : Y' ≃ₜ Y)
    (hR : R' = h ⁻¹' R) (hT : T' = k ⁻¹' T)
    (f' : C(R', T'))
    (hmap : ∀ x, k (f' x) = f ⟨h x, hR ▸ x.property⟩) :
    ChartwisePLMap (fun i => h.transOpenPartialHomeomorph (e i))
      (fun j => k.transOpenPartialHomeomorph (d j)) f' := by
  subst R'
  subst T'
  exact hf.preimage_homeomorph h k f' hmap



theorem ChartwisePLHomeomorph.transport_homeomorph
    {e : α → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {d : β → OpenPartialHomeomorph Y (Fin 3 → ℝ)}
    {R : Set X} {T : Set Y} {R' : Set X'} {T' : Set Y'}
    {f : R ≃ₜ T} (hf : ChartwisePLHomeomorph e d f)
    (h : X' ≃ₜ X) (k : Y' ≃ₜ Y)
    (hR : R' = h ⁻¹' R) (hT : T' = k ⁻¹' T)
    (f' : R' ≃ₜ T')
    (hmap : ∀ x, k (f' x) = f ⟨h x, hR ▸ x.property⟩) :
    ChartwisePLHomeomorph (fun i => h.transOpenPartialHomeomorph (e i))
      (fun j => k.transOpenPartialHomeomorph (d j)) f' := by
  subst R'
  subst T'
  exact hf.preimage_homeomorph h k f' hmap

end PoincareConjecture.M76
