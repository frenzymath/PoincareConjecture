import PoincareConjecture.Proofs.M76.Mathlib.SquareShellIncidence
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLFamilyGluing
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets











set_option autoImplicit false

open Set Geometry

namespace SquareShell




theorem exists_rotation_homeomorph {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (i : Fin 4) : ∃ A : sector a b ≃ₜ rotatedSector a b i,
      A.IsFinitePL ∧ ∀ p, (A p : ℝ × ℝ) = rotation i p := by
  obtain ⟨e, he, _⟩ := exists_sector_homeomorph ha hab
  obtain ⟨_, ⟨K, hK, hKS, _⟩, _⟩ := he.symm
  have hPL : FinitePiecewiseAffineOn (rotation i) (sector a b) :=
    ⟨K, hK, hKS, K.affineOnFaces_affine (rotation i)⟩
  have hex := hPL.exists_homeomorph_image (rotation_injective i).injOn
  rw [rotation_image] at hex
  exact hex







theorem exists_radius_homeomorph {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcd : c < d) :
    ∃ H : shell a b ≃ₜ shell c d, H.IsFinitePL ∧
      ∀ x : shell a b,
        ‖(H x : ℝ × ℝ)‖ = radiusMap a b c d ‖(x : ℝ × ℝ)‖ ∧
        (‖(x : ℝ × ℝ)‖ = a → (H x : ℝ × ℝ) = (c / a) • (x : ℝ × ℝ)) ∧
        (‖(x : ℝ × ℝ)‖ = b → (H x : ℝ × ℝ) = (d / b) • (x : ℝ × ℝ)) := by
  obtain ⟨e, he, heval⟩ := exists_sector_radius_homeomorph ha hab hc hcd
  choose A hA hAval using exists_rotation_homeomorph ha hab
  choose B hB hBval using exists_rotation_homeomorph hc hcd
  let F (i : Fin 4) := (A i).symm.trans (e.trans (B i))
  have hF (i : Fin 4) : (F i).IsFinitePL := (hA i).symm.trans (he.trans (hB i))
  have hFparam (i : Fin 4) (p : sector a b) :
      (F i (A i p) : ℝ × ℝ) = rotation i (e p) := by
    change (B i (e ((A i).symm (A i p))) : ℝ × ℝ) = _
    rw [(A i).symm_apply_apply, hBval]
  have hpoint (i : Fin 4) (x : rotatedSector a b i) :
      (x : ℝ × ℝ) = rotation i ((A i).symm x) :=
    (congrArg Subtype.val ((A i).apply_symm_apply x)).symm.trans (hAval i _)
  have hFpoint (i : Fin 4) (x : rotatedSector a b i) :
      (F i x : ℝ × ℝ) = rotation i (e ((A i).symm x)) := by
    have h := hFparam i ((A i).symm x)
    simpa only [(A i).apply_symm_apply] using h
  have hoverlap (i j : Fin 4) (x : rotatedSector a b i) :
      (x : ℝ × ℝ) ∈ rotatedSector a b j ↔ (F i x : ℝ × ℝ) ∈ rotatedSector c d j := by
    rw [hpoint i x, hFpoint]
    exact rotation_mem_transport_iff ha hc ((A i).symm x).property
      (e ((A i).symm x)).property (heval _).2.1 (heval _).2.2.1 i j
  have hagree (i j : Fin 4) (x : ℝ × ℝ)
      (hi : x ∈ rotatedSector a b i) (hj : x ∈ rotatedSector a b j) :
      (F i ⟨x, hi⟩ : ℝ × ℝ) = F j ⟨x, hj⟩ := by
    rw [hFpoint, hFpoint]
    apply rotation_transport_eq ha (fun p => (e p : ℝ × ℝ)) (radiusMap a b c d)
      (fun p => ⟨(heval p).1, (heval p).2.1.mp, (heval p).2.2.1.mp⟩)
    exact (hpoint i ⟨x, hi⟩).symm.trans (hpoint j ⟨x, hj⟩)
  obtain ⟨G, hG, hGval⟩ := Homeomorph.exists_iUnion_finitePL
    (rotatedSector a b) (rotatedSector c d) F hF hoverlap hagree
  let H := (Homeomorph.setCongr (iUnion_rotatedSector a b).symm).trans
    (G.trans (Homeomorph.setCongr (iUnion_rotatedSector c d)))
  have hHval (i : Fin 4) (x : rotatedSector a b i) :
      (H ⟨x, rotatedSector_subset_shell a b i x.property⟩ : ℝ × ℝ) = F i x :=
    hGval i x
  refine ⟨H, hG.setCongr (iUnion_rotatedSector a b) (iUnion_rotatedSector c d), ?_⟩
  intro x
  have hxunion : (x : ℝ × ℝ) ∈ ⋃ i, rotatedSector a b i := by
    rw [iUnion_rotatedSector]
    exact x.property
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxunion
  let p := (A i).symm ⟨x, hi⟩
  have hxval : (x : ℝ × ℝ) = rotation i p := hpoint i ⟨x, hi⟩
  have hHpoint : (H x : ℝ × ℝ) = rotation i (e p) :=
    (hHval i ⟨x, hi⟩).trans (hFpoint i ⟨x, hi⟩)
  have hnorm : ‖(x : ℝ × ℝ)‖ = (p : ℝ × ℝ).2 := by
    rw [hxval, norm_rotation, norm_of_mem_sector p.property]
  refine ⟨?_, ?_, ?_⟩
  · rw [hHpoint, norm_rotation, norm_of_mem_sector (e p).property, (heval p).1, hnorm]
  · intro hx
    rw [hnorm] at hx
    rw [hHpoint, (heval p).2.2.2.1 hx, rotation_smul, ← hxval]
  · intro hx
    rw [hnorm] at hx
    rw [hHpoint, (heval p).2.2.2.2 hx, rotation_smul, ← hxval]

end SquareShell
