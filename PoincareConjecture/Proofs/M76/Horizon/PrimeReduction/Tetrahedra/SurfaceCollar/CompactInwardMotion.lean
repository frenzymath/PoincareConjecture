import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalPLMotionComposition
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_compact_inward_motion
    {X ι κ : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    {R r O : Set X} (hr : IsCompact r) (hrR : r ⊆ R) (S : κ → Set X)
    (hlocal : ∀ y ∈ r, ∃ H : X ≃ₜ X,
      (∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      EqOn H id Oᶜ ∧ (∀ j x, H x ∈ S j ↔ x ∈ S j) ∧
      (∀ x ∈ R, H x ∈ interior R ∨ H x = x) ∧ H y ∈ interior R) :
    ∃ H : X ≃ₜ X,
      (∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (H.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      EqOn H id Oᶜ ∧ (∀ j x, H x ∈ S j ↔ x ∈ S j) ∧
      (∀ x ∈ R, H x ∈ interior R ∨ H x = x) ∧ H '' r ⊆ interior R := by
  classical
  choose F hFPL hFfix hFS hFin hFy using fun y : r => hlocal y y.property
  have hpres (y : r) {x : X} (hx : x ∈ interior R) : F y x ∈ interior R := by
    rcases hFin y x (interior_subset hx) with hi | heq
    · exact hi
    · exact heq.symm ▸ hx
  obtain ⟨T,hT⟩ := hr.elim_finite_subcover (fun y : r => F y ⁻¹' interior R)
    (fun y => isOpen_interior.preimage (F y).continuous)
    (fun y hy => mem_iUnion.mpr ⟨⟨y,hy⟩,hFy ⟨y,hy⟩⟩)
  have hfinite (T : Finset r) : ∃ H : X ≃ₜ X,
      (∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      EqOn H id Oᶜ ∧ (∀ j x, H x ∈ S j ↔ x ∈ S j) ∧
      (∀ x ∈ R, H x ∈ interior R ∨ H x = x) ∧
      ∀ y ∈ T, ∀ x ∈ R, F y x ∈ interior R → H x ∈ interior R := by
    induction T using Finset.induction_on with
    | empty =>
      refine ⟨Homeomorph.refl X,?_,fun _ _ => rfl,fun _ _ => Iff.rfl,
        fun _ _ => Or.inr rfl,?_⟩
      · intro i j
        simpa using he i j
      · simp
    | @insert y T hy ih =>
      obtain ⟨H,hHPL,hHfix,hHS,hHin,hHT⟩ := ih
      refine ⟨H.trans (F y),original_PL_motion_trans e hcover H (F y) hHPL (hFPL y),
        ?_,?_,?_,?_⟩
      · intro x hx
        change F y (H x) = x
        rw [hHfix hx,id_eq]
        exact hFfix y hx
      · intro j x
        exact (hFS y j (H x)).trans (hHS j x)
      · intro x hx
        change F y (H x) ∈ interior R ∨ F y (H x) = x
        rcases hHin x hx with hi | hf
        · exact Or.inl (hpres y hi)
        · rw [hf]
          exact hFin y x hx
      · intro z hz x hx hzF
        change F y (H x) ∈ interior R
        rcases Finset.mem_insert.mp hz with rfl | hz
        · rcases hHin x hx with hi | hf
          · exact hpres z hi
          · rwa [hf]
        · exact hpres y (hHT z hz x hx hzF)
  obtain ⟨H,hHPL,hHfix,hHS,hHin,hHT⟩ := hfinite T
  refine ⟨H,hHPL,?_,hHfix,hHS,hHin,?_⟩
  · intro i j
    have hinv := (piecewiseAffineGroupoid V3).symm (hHPL j i)
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm,OpenPartialHomeomorph.trans_assoc,
      Homeomorph.symm_toOpenPartialHomeomorph] using hinv
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hyT,hyx⟩ := mem_iUnion₂.mp (hT hx)
    exact hHT y hyT x (hrR hx) hyx

end PoincareConjecture.M76
