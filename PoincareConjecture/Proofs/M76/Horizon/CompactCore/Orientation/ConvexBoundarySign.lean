import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.AffineBoundarySign
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import Mathlib.Analysis.Convex.Intrinsic











set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem plLocalSign_eq_of_convex_boundary_piece
    (h : OpenPartialHomeomorph E E) (hh : h ∈ piecewiseAffineGroupoid E)
    (ell m : E →ᴬ[ℝ] ℝ) (n n' : E) (B : E →ᴬ[ℝ] E)
    (hn : ell.contLinear n = 1) (hn' : m.contLinear n' = 1)
    (s : Set E) (hs : Convex ℝ s) (hne : s.Nonempty) (hsource : s ⊆ h.source)
    (hspan : (affineSpan ℝ s : Set E) = {y | ell y = 0})
    (hside : ∀ y ∈ h.source, 0 ≤ m (h y) ↔ 0 ≤ ell y)
    (hagree : EqOn h B s) (x : h.source) (hx : (x : E) ∈ intrinsicInterior ℝ s) :
    plLocalSign h hh x =
      SignType.sign (LinearMap.det (affineNormalExtension ell n n' B).toAffineMap.linear) := by
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro he
    have hz : ell.contLinear n = 0 := congrArg (fun L : E →ₗ[ℝ] ℝ => L n) he
    rw [hn] at hz
    norm_num at hz
  have hm : m.toAffineMap.linear ≠ 0 := by
    intro he
    have hz : m.contLinear n' = 0 := congrArg (fun L : E →ₗ[ℝ] ℝ => L n') he
    rw [hn'] at hz
    norm_num at hz
  have hfr := h.isImage_frontier_of_affine_nonneg m hm
    (fun y hy => (hside y hy).symm)
  have hfrell := (OpenPartialHomeomorph.refl E).isImage_frontier_of_affine_nonneg
    ell hell (K := {y | 0 ≤ ell y}) (fun _ _ => Iff.rfl)
  have hz (y : E) (hy : y ∈ s) : ell y = 0 := by
    have := mem_affineSpan ℝ hy
    rwa [← SetLike.mem_coe, hspan] at this
  have hzero : EqOn (m.toAffineMap.comp B.toAffineMap) (AffineMap.const ℝ E 0) s := by
    intro y hy
    change m (B y) = 0
    rw [← hagree hy]
    exact (hfr.apply_mem_iff (hsource hy)).mpr
      ((hfrell.apply_mem_iff (mem_univ y)).mp (hz y hy))
  have hB : ∀ y, ell y = 0 → m (B y) = 0 := by
    intro y hy
    apply AffineMap.eqOn_affineSpan hzero
    rwa [hspan]
  have hi : InjOn B {y | ell y = 0} := by
    rw [← hspan]
    apply B.toAffineMap.injOn_affineSpan_of_injOn_convex hs hne
    intro y hy z hz' heq
    exact h.injOn (hsource hy) (hsource hz')
      ((hagree hy).trans (heq.trans (hagree hz').symm))
  obtain ⟨y, hy, hyx⟩ := mem_intrinsicInterior.mp hx
  obtain ⟨U, hU, hUi⟩ := isOpen_induced_iff.mp
    (isOpen_interior : IsOpen (interior ((↑) ⁻¹' s : Set (affineSpan ℝ s))))
  have hxU : (x : E) ∈ U := by
    rw [← hyx]
    change y ∈ (Subtype.val : affineSpan ℝ s → E) ⁻¹' U
    rwa [hUi]
  have hUs : ∀ z ∈ U, ell z = 0 → z ∈ s := by
    intro z hzU hz0
    have hzs : z ∈ affineSpan ℝ s := by rwa [← SetLike.mem_coe, hspan]
    have hzi : (⟨z, hzs⟩ : affineSpan ℝ s) ∈ interior ((↑) ⁻¹' s) := by
      rw [← hUi]
      exact hzU
    exact (interior_subset hzi : (⟨z, hzs⟩ : affineSpan ℝ s) ∈ (↑) ⁻¹' s)
  let r := h.restr U
  have hr : r ∈ piecewiseAffineGroupoid E := closedUnderRestriction' hh hU
  have hxr : (x : E) ∈ r.source := ⟨x.property, by simpa [hU.interior_eq] using hxU⟩
  have hx0 := hz x (intrinsicInterior_subset hx)
  have hsign := plLocalSign_eq_affineNormalExtension r hr ell m n n' B hn hn'
    hB hi (fun z hz => hside z hz.1)
    (fun z hz he => hagree (hUs z (interior_subset hz.2) he)) ⟨x, hxr⟩ hx0
  exact (plLocalSign_restr h hh hU ⟨x, hxr⟩).symm.trans hsign

theorem plLocalSign_mul_boundary_det_sign
    (b : Module.Basis (Fin 3) ℝ E)
    (h : OpenPartialHomeomorph E E) (hh : h ∈ piecewiseAffineGroupoid E)
    (ell m : E →ᴬ[ℝ] ℝ) (n n' : E) (B : E →ᴬ[ℝ] E)
    (hn : ell.contLinear n = 1) (hn' : m.contLinear n' = 1)
    (s : Set E) (hs : Convex ℝ s) (hne : s.Nonempty) (hsource : s ⊆ h.source)
    (hspan : (affineSpan ℝ s : Set E) = {y | ell y = 0})
    (hside : ∀ y ∈ h.source, 0 ≤ m (h y) ↔ 0 ≤ ell y)
    (hagree : EqOn h B s) (x : h.source) (hx : (x : E) ∈ intrinsicInterior ℝ s)
    (p : Fin 3 → E) (hp : ∀ i, p i ∈ s) :
    plLocalSign h hh x * SignType.sign (b.det ![p 1 - p 0, p 2 - p 0, n]) =
      SignType.sign (b.det ![B (p 1) - B (p 0), B (p 2) - B (p 0), n']) := by
  have hp0 (i : Fin 3) : ell (p i) = 0 := by
    have hi := mem_affineSpan ℝ (hp i)
    rwa [← SetLike.mem_coe, hspan] at hi
  rw [plLocalSign_eq_of_convex_boundary_piece h hh ell m n n' B hn hn'
    s hs hne hsource hspan hside hagree x hx,
    affineNormalExtension_boundary_det b ell n n' B hn p hp0,
    sign_mul]

end Geometry
