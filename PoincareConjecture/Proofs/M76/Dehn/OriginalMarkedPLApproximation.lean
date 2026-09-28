import PoincareConjecture.Proofs.M76.Dehn.OriginalCompactPairModel
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.MarkedPolyhedronHomotopy
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInCharts












set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {U M E ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [FiniteDimensional ℝ U] [TopologicalSpace M] [T2Space M]
  [LocallyCompactSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem exists_original_marked_PL_approximation
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    {R : Set M} (hR : IsClosed R)
    (hboundary : ∀ x ∈ frontier R,
      ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y))
    (S : SimplicialComplex ℝ U) (hS : S.faces.Finite) (v₀ : S.space)
    (f : C(S.space, R)) (B : Set S.space) (hB : IsCompact B)
    (F : Set M) (hF : F ⊆ frontier R)
    (hFopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' F))
    (hBF : MapsTo (fun x : S.space => (f x : M)) B F) :
    ∃ (g : U → M) (a : C(S.space, R)),
      PolyhedralPLInCharts e g S.space ∧
      (∀ x : S.space, g x = (a x : M)) ∧
      ∃ H : f.Homotopy a,
        ∀ (t : unitInterval) (x : S.space), x ∈ B → (H (t, x) : M) ∈ F := by
  classical
  let : CompactSpace S.space := isCompact_iff_compactSpace.mp (S.isCompact_space_of_finite hS)
  let fM : C(S.space, M) := ⟨fun x => (f x : M), continuous_subtype_val.comp f.continuous⟩
  have himage : IsCompact (range fM) := isCompact_range fM.continuous
  have himageR : range fM ⊆ R := by
    rintro y ⟨x, rfl⟩
    exact (f x).property
  obtain ⟨s, G, C, P, Z, H, _, hAC, hP, hZP, _, _, _, _, hH,
      hboundaryModel, hcharts⟩ :=
    exists_compact_original_PL_pair_model e hcompat hcover hR himage himageR hboundary
  have hfC (x : S.space) : (f x : M) ∈ C := interior_subset (hAC ⟨x, rfl⟩)
  let fC : C(S.space, (C ∩ R : Set M)) :=
    ⟨fun x => ⟨(f x : M), hfC x, (f x).property⟩, fM.continuous.subtype_mk _⟩
  let fP : C(S.space, P.space) :=
    ⟨fun x => H (fC x), H.continuous.comp fC.continuous⟩
  let back : C(P.space, R) :=
    ⟨fun y => ⟨(H.symm y : M), (H.symm y).property.2⟩,
      (continuous_subtype_val.comp H.symm.continuous).subtype_mk _⟩
  have hback (y : P.space) : G (H.symm y) = (y : (s → ℝ × E) × ℝ) :=
    (hH (H.symm y)).symm.trans
      (congrArg Subtype.val (H.apply_symm_apply y))
  have hbackBoundary (y : P.space) :
      (y : (s → ℝ × E) × ℝ) ∈ Z.space ↔ (H.symm y : M) ∈ frontier R := by
    simpa only [Homeomorph.apply_symm_apply] using hboundaryModel (H.symm y)
  let u : ((s → ℝ × E) × ℝ) → M := Function.extend
    (Subtype.val : P.space → (s → ℝ × E) × ℝ)
    (fun y => (H.symm y : M)) (fun _ => (f v₀ : M))
  have hu (y : P.space) : u y = (H.symm y : M) :=
    Subtype.val_injective.extend_apply _ _ y
  let iZ : C(Z.space, P.space) :=
    ⟨fun z => ⟨z.val, SimplicialComplex.space_subset_of_le hZP z.property⟩,
      continuous_subtype_val.subtype_mk _⟩
  let zback : C(Z.space, frontier R) :=
    ⟨fun z => ⟨(H.symm (iZ z) : M), (hbackBoundary (iZ z)).mp z.property⟩,
      (continuous_subtype_val.comp (H.symm.continuous.comp iZ.continuous)).subtype_mk _⟩
  let O : Set ((s → ℝ × E) × ℝ) := u ⁻¹' F
  have hO : IsOpen ((Subtype.val : Z.space → (s → ℝ × E) × ℝ) ⁻¹' O) := by
    have heq : (Subtype.val : Z.space → (s → ℝ × E) × ℝ) ⁻¹' O =
        zback ⁻¹' ((Subtype.val : frontier R → M) ⁻¹' F) := by
      ext z
      change u (iZ z) ∈ F ↔ (H.symm (iZ z) : M) ∈ F
      rw [hu (iZ z)]
    rw [heq]
    exact hFopen.preimage zback.continuous
  have hBO : MapsTo (fun x : S.space => (fP x : (s → ℝ × E) × ℝ)) B (O ∩ Z.space) := by
    intro x hx
    refine ⟨?_, (hboundaryModel (fC x)).mpr (hF (hBF hx))⟩
    change u (fP x) ∈ F
    rw [hu]
    change (H.symm (H (fC x)) : M) ∈ F
    rw [H.symm_apply_apply]
    exact hBF hx
  obtain ⟨q, aP, hq, haP, eta, heta⟩ :=
    S.exists_marked_finitePL_homotopy hS P Z hP hZP fP B hB O hO hBO
  let g : U → M := u ∘ q
  let a : C(S.space, R) := back.comp aP
  have hga (x : S.space) : g x = (a x : M) := by
    change u (q x) = (H.symm (aP x) : M)
    rw [← haP x, hu]
  have hgc : ContinuousOn g S.space := continuousOn_iff_continuous_domRestrict.mpr
    ((continuous_subtype_val.comp a.continuous).congr (fun x => (hga x).symm))
  have hgC : MapsTo g S.space C := by
    intro x hx
    rw [hga ⟨x, hx⟩]
    exact (H.symm (aP ⟨x, hx⟩)).property.1
  have hGg : EqOn (G ∘ g) q S.space := by
    intro x hx
    change G (g x) = q x
    rw [hga ⟨x, hx⟩]
    exact (hback (aP ⟨x, hx⟩)).trans (haP ⟨x, hx⟩)
  have hg : PolyhedralPLInCharts e g S.space :=
    polyhedralPLInCharts_of_affine_projections e G C hcharts S hS hgc hgC hq hGg
  have hstart : back.comp fP = f := by
    ext x
    change (H.symm (H (fC x)) : M) = (f x : M)
    rw [H.symm_apply_apply]
    rfl
  let etaM : f.Homotopy a := ((ContinuousMap.Homotopy.refl back).comp eta).cast hstart rfl
  refine ⟨g, a, hg, hga, etaM, ?_⟩
  intro t x hx
  have h := (heta t x hx).1
  change u (eta (t, x)) ∈ F at h
  rw [hu] at h
  exact h

end OpenPartialHomeomorph
