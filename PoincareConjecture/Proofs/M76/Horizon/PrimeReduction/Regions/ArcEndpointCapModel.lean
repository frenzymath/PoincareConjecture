import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.ArcEndpointCaps
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.MarkedHalfspaceModel









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_arc_endpoint_cap_model
    {κ : Type*} [Finite κ]
    (B : Fin 2 → OpenPartialHomeomorph V3 V3)
    (hB : ∀ i, B i ∈ piecewiseAffineGroupoid V3)
    (p : Fin 2 → V3) (hp : ∀ i, p i ∈ (B i).source)
    (hBp : ∀ i, B i (p i) = 0)
    (hdis : Pairwise (fun i j => Disjoint (B i).source (B j).source))
    (A : Set V3) (hA : IsCompact A)
    (haxis : ∀ i x, x ∈ (B i).source →
      (x ∈ A ↔ B i x 0 = 0 ∧ B i x 1 = 0 ∧ 0 ≤ B i x 2))
    {W : Set V3} (hW : IsOpen W) (hAW : A ⊆ W)
    (P : κ → SimplicialComplex ℝ V3) (hP : ∀ i, (P i).faces.Finite) :
    ∃ (R : Set V3) (K : SimplicialComplex ℝ V3)
      (M : Sum Bool κ → SimplicialComplex ℝ V3) (V : Fin 2 → Set V3),
      IsClosed R ∧ A ⊆ R ∧ A ∩ frontier R = {p 0, p 1} ∧
      A \ {p 0, p 1} ⊆ interior R ∧
      K.faces.Finite ∧ A ⊆ interior K.space ∧ K.space ⊆ W ∧
      K.space ⊆ (⋃ i, V i) ∪ interior R ∧
      (∀ i, IsOpen (V i) ∧ p i ∈ V i ∧ V i ⊆ (B i).source ∩ W ∧
        (∀ x ∈ V i, x ∈ R ↔ 0 ≤ B i x 2) ∧
        ∀ x ∈ V i, x ∈ frontier R ↔ B i x 2 = 0) ∧
      (∀ i, M i ≤ K ∧ (M i).faces.Finite ∧
        ∀ f ∈ K.faces, (∀ v ∈ f, v ∈ (M i).vertices) → f ∈ (M i).faces) ∧
      (M (.inl false)).space = K.space ∩ R ∧
      (M (.inl true)).space = K.space ∩ frontier R ∧
      ∀ i, (M (.inr i)).space = K.space ∩ R ∩ (P i).space := by
  classical
  have hpA (i : Fin 2) : p i ∈ A :=
    (haxis i (p i) (hp i)).mpr (by simp only [hBp, Pi.zero_apply, le_refl, and_self])
  obtain ⟨R, r, caps, N, V, _, hR, hcap, hAR, hAF, hAI, hAV⟩ :=
    exists_arc_endpoint_cap_region B hB p hp hBp hdis A haxis
      (fun _ => W) (fun _ => hW) (fun i => hAW (hpA i))
  have hV (i : Fin 2) : IsOpen (V i) ∧ p i ∈ V i ∧ V i ⊆ (B i).source ∩ W ∧
      (∀ x ∈ V i, x ∈ R ↔ 0 ≤ B i x 2) ∧
      ∀ x ∈ V i, x ∈ frontier R ↔ B i x 2 = 0 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hi⟩ := hcap i
    exact hi
  let O := W ∩ ((⋃ i, V i) ∪ interior R)
  have hO : IsOpen O :=
    hW.inter ((isOpen_iUnion (fun i => (hV i).1)).union isOpen_interior)
  have hAO : A ⊆ O := fun x hx => ⟨hAW hx, hAV hx⟩
  have hcharts : ∀ x ∈ O, ∃ Q : OpenPartialHomeomorph V3 V3,
      x ∈ Q.source ∧ LocallyPiecewiseAffineOn Q Q.source ∧
      (Q.source ⊆ interior R ∨
        ∃ (ell : V3 →ᴬ[ℝ] ℝ), ell.toAffineMap.linear ≠ 0 ∧
          ∀ y ∈ Q.source, y ∈ R ↔ 0 ≤ ell (Q y)) := by
    intro x hx
    rcases hx.2 with hx | hx
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      let Q := (B i).restrOpen (V i) (hV i).1
      have hQ : LocallyPiecewiseAffineOn Q Q.source :=
        ((mem_piecewiseAffineGroupoid_iff V3 (B i)).mp (hB i)).1.mono
          Q.open_source (fun _ hy => hy.1)
      let ell : V3 →ᴬ[ℝ] ℝ := (ContinuousLinearMap.proj (2 : Fin 3)).toContinuousAffineMap
      have hell : ell.toAffineMap.linear ≠ 0 := by
        intro hz
        have hh := congrArg (fun f : V3 →ₗ[ℝ] ℝ => f (fun _ => 1)) hz
        change (1 : ℝ) = 0 at hh
        norm_num at hh
      exact ⟨Q, ⟨((hV i).2.2.1 hxi).1, hxi⟩, hQ,
        Or.inr ⟨ell, hell, fun y hy => (hV i).2.2.2.1 y hy.2⟩⟩
    · let Q := (OpenPartialHomeomorph.refl V3).restrOpen (interior R) isOpen_interior
      refine ⟨Q, ⟨mem_univ x, hx⟩, ?_, Or.inl (fun _ hy => hy.2)⟩
      exact (locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ V3) isOpen_univ).mono
        Q.open_source (fun _ _ => mem_univ _)
  obtain ⟨K, M, hK, hAK, hKO, hM, hreg, hfr, hsource⟩ :=
    exists_marked_local_halfspace_model hA hO hAO hcharts P hP
  exact ⟨R, K, M, V, hR, hAR, hAF, hAI, hK, hAK,
    fun _ hx => (hKO hx).1, fun _ hx => (hKO hx).2,
    hV, hM, hreg, hfr, hsource⟩

end PoincareConjecture.M76
