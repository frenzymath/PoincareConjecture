import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Disks.NonnegativeNormalDisplacement











set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76





theorem exists_protected_separated_circle_caps
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T P M : SimplicialComplex ℝ E)
    (hT : T.faces.Finite) (hP : P.faces.Finite) (hM : M.faces.Finite)
    (hTP : T.space ⊆ P.space) (hTM : Disjoint T.space M.space)
    {O : Set E} (hO : IsOpen O) (hTO : T.space ⊆ O)
    (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0)
    (R r : Bool → Set E)
    (hR : ∀ b, IsFinitePLBallPair (ℝ × ℝ) (R b) (r b))
    (hRP : ∀ b, R b ⊆ P.space) (hRO : ∀ b, R b ⊆ O)
    (hRM : ∀ b, R b ∩ M.space = r b)
    (hpositive : ∀ x ∈ R true, 0 ≤ A x) (hnegative : ∀ x ∈ R false, A x ≤ 0)
    (hplanar : ∀ b x, x ∈ R b → A x = 0 → x ∈ T.space) :
    ∃ (U : Set E) (F : Bool → E ≃ₜ E),
      IsOpen U ∧ T.space ⊆ U ∧ U ⊆ O ∧ Disjoint U M.space ∧
      (∀ b, (∀ x, x ∉ U → F b x = x) ∧
        EqOn (F b) id M.space ∧ EqOn (F b).symm id M.space ∧
        (∀ x, x ∉ O → F b x = x) ∧ EqOn (F b) id (r b) ∧
        IsFinitePLBallPair (ℝ × ℝ) (F b '' R b) (r b) ∧
        F b '' R b ⊆ O ∧ (F b '' R b) ∩ M.space = r b ∧
        ∀ x ∈ R b, if b then 0 < A (F b x) else A (F b x) < 0) ∧
      Disjoint (F true '' R true) (F false '' R false) := by
  let U : Set E := O \ M.space
  have hU : IsOpen U := hO.sdiff (M.isCompact_space_of_finite hM).isClosed
  have hTU : T.space ⊆ U := fun x hx =>
    ⟨hTO hx, fun hxM => Set.disjoint_left.mp hTM hx hxM⟩
  have hUM : Disjoint U M.space := Set.disjoint_left.mpr (fun _ hx hxM => hx.2 hxM)
  have hrM (b : Bool) : r b ⊆ M.space := fun _ hx => ((hRM b).symm.subset hx).2
  have hrU (b : Bool) : Disjoint (r b) U :=
    Set.disjoint_left.mpr (fun _ hx hxU => hxU.2 (hrM b hx))
  obtain ⟨F, hF, hdisjoint⟩ := exists_separated_normal_cap_pair T P hT hP hTP
    hU hTU A hA R r hR hRP hrU hpositive hnegative hplanar
  refine ⟨U, F, hU, hTU, fun _ hx => hx.1, hUM, ?_, hdisjoint⟩
  intro b
  obtain ⟨hfix, hrfix, hball, hsign⟩ := hF b
  have hfixM (x : E) (hx : x ∈ M.space) : F b x = x :=
    hfix x (fun hxU => hxU.2 hx)
  have hfixO (x : E) (hx : x ∉ O) : F b x = x :=
    hfix x (fun hxU => hx hxU.1)
  refine ⟨hfix, hfixM, ?_, hfixO, hrfix, hball, ?_, ?_, hsign⟩
  · intro x hx
    exact (F b).symm_apply_eq.mpr (hfixM x hx).symm
  · rintro _ ⟨x, hx, rfl⟩
    by_contra hn
    have heq : F b (F b x) = F b x := hfixO _ hn
    have hxfx : F b x = x := (F b).injective heq
    exact hn (hxfx.symm ▸ hRO b hx)
  · apply Subset.antisymm
    · rintro y ⟨⟨x, hx, hxy⟩, hyM⟩
      have hxy' : x = y := (F b).injective (hxy.trans (hfixM y hyM).symm)
      exact (hRM b).subset ⟨hxy' ▸ hx, hyM⟩
    · intro y hy
      exact ⟨⟨y, (hR b).1 hy, hrfix hy⟩, hrM b hy⟩

end PoincareConjecture.M76
