import PoincareConjecture.Proofs.M76.Wall.Mathlib.OriginalExteriorSubcomplex
import PoincareConjecture.Proofs.M76.RelativeApproximation.ModelInverse











set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1






theorem exists_original_arc_exterior_model
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph X V3)
    {C L : Set X} (hC : IsCompact C) (hL : IsClosed L)
    {q : ℝ → X} (hcore : L ∪ q '' I ⊆ interior C)
    (hzero : q 0 ∈ frontier L) (hone : q 1 ∈ frontier L)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, q t ∉ L)
    (S : Fin 2 → Set X) (hSL : ∀ i, S i ⊆ frontier L)
    (K P D A : SimplicialComplex ℝ E) (B : Fin 2 → SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hPK : P ≤ K) (hDK : D ≤ K) (hAK : A ≤ K)
    (hBK : ∀ i, B i ≤ K) (F : X → E) (hF : Continuous F)
    (H : C ≃ₜ K.space) (g : E → C)
    (hHF : ∀ x : C, (H x : E) = F x)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hP : P.space = F '' L) (hD : D.space = F '' frontier L)
    (hA : A.space = F '' (q '' I)) (hB : ∀ i, (B i).space = F '' S i)
    (hcharts : ∀ x ∈ C, ∃ (i : ι) (V : Set X) (a : E →ᴬ[ℝ] V3),
      IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ F) (e i) V) :
    ∃ (N : SimplicialComplex ℝ E) (J : (C \ interior L : Set X) ≃ₜ N.space)
      (v : E → (C \ interior L : Set X)),
      N ≤ K ∧ N.faces.Finite ∧ N.space = F '' (C \ interior L) ∧
      D ≤ N ∧ A ≤ N ∧ (∀ i, B i ≤ N) ∧
      (∀ x : (C \ interior L : Set X), (J x : E) = F x) ∧
      ContinuousOn v N.space ∧
      (∀ z : N.space, (v z : X) = (J.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z => (v z : X)) N.space ∧
      ∀ z ∈ N.space, (v z : X) = (g z : X) := by
  have hLC : L ⊆ interior C := fun _ hx => hcore (Or.inl hx)
  have hqC : MapsTo q I C := fun t ht =>
    interior_subset (hcore (Or.inr ⟨t, ht, rfl⟩))
  have hfront : frontier L ⊆ C \ interior L :=
    fun _ hx => ⟨interior_subset (hLC (hL.frontier_subset hx)), hx.2⟩
  have hqext : q '' I ⊆ C \ interior L := by
    rintro x ⟨t, ht, rfl⟩
    refine ⟨hqC ht, ?_⟩
    by_cases ht0 : t = 0
    · subst t
      exact hzero.2
    by_cases ht1 : t = 1
    · subst t
      exact hone.2
    intro htL
    exact hproper t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
      (interior_subset htL)
  obtain ⟨N, J, hNK, hN, hNs, hJF, hmarks⟩ :=
    exists_originalExterior_subcomplex hC hLC K P hK hPK F hF H hHF hP
  have hDN : D ≤ N := hmarks D hDK (hD.subset.trans (image_mono hfront))
  have hAN : A ≤ N := hmarks A hAK (hA.subset.trans (image_mono hqext))
  have hBN (i : Fin 2) : B i ≤ N :=
    hmarks (B i) (hBK i) ((hB i).subset.trans (image_mono ((hSL i).trans hfront)))
  let x0 : (C \ interior L : Set X) := ⟨q 0, hfront hzero⟩
  obtain ⟨v, hvc, hv, hvPL⟩ := exists_polyhedral_PL_model_inverse e N hN J F
    (Subset.refl (C \ interior L)) x0 hJF (fun x hx => hcharts x hx.1)
  have hgF (x : X) (hx : x ∈ C) : (g (F x) : X) = x := by
    have h := hg (H ⟨x, hx⟩)
    rw [H.symm_apply_apply] at h
    simpa only [hHF] using h
  refine ⟨N, J, v, hNK, hN, hNs, hDN, hAN, hBN, hJF, hvc, hv, hvPL, ?_⟩
  intro z hz
  have hFJ : F (J.symm ⟨z, hz⟩) = z :=
    (hJF (J.symm ⟨z, hz⟩)).symm.trans
      (congrArg Subtype.val (J.apply_symm_apply ⟨z, hz⟩))
  have hgJ := hgF (J.symm ⟨z, hz⟩) (J.symm ⟨z, hz⟩).property.1
  rw [hFJ] at hgJ
  exact (hv ⟨z, hz⟩).trans hgJ.symm

end PoincareConjecture.M76
