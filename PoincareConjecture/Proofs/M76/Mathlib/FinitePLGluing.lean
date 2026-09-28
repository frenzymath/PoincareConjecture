import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.CompactHomeomorphGluing










set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]





theorem finitePiecewiseAffineOn_of_finite_cover (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {ι : Type*} [Finite ι]
    (J : ι → SimplicialComplex ℝ E) (hJ : ∀ i, (J i).faces.Finite)
    {f : E → F} (hf : ∀ i, (J i).AffineOnFaces f)
    (hcover : K.space ⊆ ⋃ i, (J i).space) : FinitePiecewiseAffineOn f K.space := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let : ∀ i, Fintype (J i).faces := fun i => (hJ i).fintype
  let T : (Σ i, (J i).faces) → Finset E := fun p => p.2.val
  let N := hK.toFinset.sup Finset.card
  have hN (r : Finset E) (hr : r ∈ K.faces) : r.card ≤ N + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hr)).trans (Nat.le_succ N)
  have hT (p : Σ i, (J i).faces) : AffineIndependent ℝ ((↑) : T p → E) :=
    (J p.1).indep p.2.property
  have hcov (x : E) (hx : x ∈ K.space) : ∃ p, x ∈ convexHull ℝ (T p : Set E) := by
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
    obtain ⟨r, hr, hxr⟩ := SimplicialComplex.mem_space_iff.mp hxi
    exact ⟨⟨i, r, hr⟩, hxr⟩
  obtain ⟨R, hR, hRK, _, href⟩ :=
    K.exists_subdivision_refines_finite_cover hK hN T hT hcov
  refine ⟨R, hR, hRK.space_eq, ?_⟩
  intro r hr
  obtain ⟨p, hp⟩ := href r hr
  obtain ⟨a, ha⟩ := hf p.1 p.2.val p.2.property
  exact ⟨a, ha.mono hp⟩



theorem FinitePiecewiseAffineOn.union {f : E → F} {s u : Set E}
    (hs : FinitePiecewiseAffineOn f s) (hu : FinitePiecewiseAffineOn f u)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hspace : K.space = s ∪ u) :
    FinitePiecewiseAffineOn f (s ∪ u) := by
  obtain ⟨S, hS, rfl, hfS⟩ := hs
  obtain ⟨U, hU, rfl, hfU⟩ := hu
  let J : Bool → SimplicialComplex ℝ E := fun b => if b then S else U
  have hJ (b : Bool) : (J b).faces.Finite := by cases b <;> assumption
  have hfJ (b : Bool) : (J b).AffineOnFaces f := by cases b <;> assumption
  have hcover : K.space ⊆ ⋃ b, (J b).space := by
    intro x hx
    rw [hspace] at hx
    rcases hx with hx | hx
    · exact mem_iUnion.mpr ⟨true, hx⟩
    · exact mem_iUnion.mpr ⟨false, hx⟩
  rw [← hspace]
  exact finitePiecewiseAffineOn_of_finite_cover K hK J hJ hfJ hcover

end Geometry

namespace Homeomorph





theorem exists_union_of_isFinitePL {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s u : Set E} {t v : Set F} (e : s ≃ₜ t) (d : u ≃ₜ v)
    (he : e.IsFinitePL) (hd : d.IsFinitePL)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hspace : K.space = s ∪ u)
    (hoverlap : ∀ x : s, (x : E) ∈ u ↔ (e x : F) ∈ v)
    (hagree : ∀ (x : E) (hxs : x ∈ s) (hxu : x ∈ u),
      (e ⟨x, hxs⟩ : F) = (d ⟨x, hxu⟩ : F)) :
    ∃ H : (s ∪ u : Set E) ≃ₜ (t ∪ v : Set F), H.IsFinitePL ∧
      (∀ x : s, (H ⟨x, Or.inl x.property⟩ : F) = e x) ∧
      (∀ x : u, (H ⟨x, Or.inr x.property⟩ : F) = d x) := by
  classical
  obtain ⟨f, hf, hef⟩ := he
  obtain ⟨g, hg, hdg⟩ := hd
  obtain ⟨H, hHs, hHu⟩ := exists_union_of_compact hf.isCompact hg.isCompact e d hoverlap hagree
  let h : E → F := fun x => if hx : x ∈ s ∪ u then H ⟨x, hx⟩ else 0
  have hh (x : (s ∪ u : Set E)) : h x = (H x : F) := by
    dsimp only [h]
    rw [dif_pos x.property]
  have hfs : EqOn f h s := by
    intro x hx
    exact (hef ⟨x, hx⟩).symm.trans ((hHs ⟨x, hx⟩).symm.trans (hh ⟨x, Or.inl hx⟩).symm)
  have hgu : EqOn g h u := by
    intro x hx
    exact (hdg ⟨x, hx⟩).symm.trans ((hHu ⟨x, hx⟩).symm.trans (hh ⟨x, Or.inr hx⟩).symm)
  exact ⟨H, ⟨h, (hf.congr hfs).union (hg.congr hgu) K hK hspace,
    fun x => (hh x).symm⟩, hHs, hHu⟩

end Homeomorph
