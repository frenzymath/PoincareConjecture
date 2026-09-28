import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Carrier
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.RegularLevel

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem exists_regular_boundary_intersection_subcomplex
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (K G : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hG : G.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (S : Set X) (rim : Set E) (hrim : IsCompact rim) (hrimK : rim ⊆ K.space)
    (hGs : G.space = {x | x ∈ K.space ∧ g x ∈ S})
    (hboundary : ∀ x ∈ G.space ∩ rim,
      Nonempty (OriginalSurfacePairChart e S (g '' K.space) (g x) true))
    {z : E → ℝ} (hz : FinitePiecewiseAffineOn z K.space)
    (hznonneg : ∀ x ∈ K.space, 0 ≤ z x)
    (hzzero : ∀ x ∈ K.space, z x = 0 ↔ x ∈ rim)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (c : ℝ) (R M P : SimplicialComplex ℝ E),
      0 < c ∧ c < δ ∧ R.faces.Finite ∧ R.IsSubdivision K ∧
      R.space = K.space ∧ M ≤ R ∧ M.faces.Finite ∧
      M.space = K.space ∩ {x | z x ≤ c} ∧ rim ⊆ M.space ∧
      (∀ s ∈ R.faces, (∀ v ∈ s, v ∈ M.vertices) → s ∈ M.faces) ∧
      P.faces.Finite ∧ (∀ s ∈ P.faces, s.card ≤ 2) ∧ P.AffineOnFaces z ∧
      (∀ v ∈ P.vertices, z v ≠ c) ∧
      (G.space ∩ {x | z x = c}).Finite ∧
      (G.space ∩ {x | z x = c} = P.space ∩ {x | z x = c}) ∧
      ∀ x ∈ G.space ∩ {x | z x = c}, ∃ s ∈ P.faces, s.card = 2 ∧
        x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  classical
  obtain ⟨ε, M₀, H, hε, hεδ, hM₀, _, hM₀s, hHs, _, _, hzH, lines, hdim, hcover⟩ :=
    exists_finite_boundary_intersection_collar K G hK hG hg hgi S rim hrim hrimK
      hGs hboundary hz hznonneg hzzero hδ
  obtain ⟨c, P, hc, hP, hPs, hPc, hPz, hreg, hfinite, hpoints⟩ :=
    exists_regular_finitePL_level_in_line_carrier hzH lines hdim hcover hε
  have hlevel : G.space ∩ {x | z x = c} = H.space ∩ {x | z x = c} := by
    ext x
    constructor
    · rintro ⟨hxG, hxc⟩
      refine ⟨hHs.symm.subset ⟨hxG, hM₀s.symm.subset ⟨(hGs.subset hxG).1, ?_⟩⟩, hxc⟩
      change z x ≤ ε
      rw [hxc]
      exact hc.2.le
    · rintro ⟨hxH, hxc⟩
      exact ⟨(hHs.subset hxH).1, hxc⟩
  let shift : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.id ℝ ℝ - ContinuousAffineMap.const ℝ ℝ c
  have hzshift : FinitePiecewiseAffineOn (fun x => z x - c) K.space := hz.postcomp shift
  obtain ⟨R, Plus, Minus, hR, hRK, hRs, hsides⟩ :=
    K.exists_subdivision_with_finitePL_signed_sides hK (fun _ : Unit => K.space)
      (fun _ x => z x - c) (fun _ => hzshift) (fun _ => subset_refl _)
  obtain ⟨_, hMR, _, hM, _, hMs, _, _, _, hfull⟩ := hsides ()
  have hMspace : (Minus ()).space = K.space ∩ {x | z x ≤ c} := by
    simpa only [sub_nonpos] using hMs
  refine ⟨c, R, Minus (), P, hc.1, hc.2.trans hεδ, hR, hRK, hRs, hMR, hM,
    hMspace, ?_, hfull, hP, hPc, hPz, hreg, hlevel.symm ▸ hfinite,
    hlevel.trans (by rw [hPs]), ?_⟩
  · intro x hx
    apply hMspace.symm.subset
    refine ⟨hrimK hx, ?_⟩
    change z x ≤ c
    rw [(hzzero x (hrimK hx)).mpr hx]
    exact hc.1.le
  · intro x hx
    exact hpoints x (hlevel.subset hx)

end PoincareConjecture.M76
