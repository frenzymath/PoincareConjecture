import PoincareConjecture.Proofs.M76.Triangulation.CubeSphereLargeDisks
import PoincareConjecture.Proofs.M76.Mathlib.ConvexSpherePoleNormalization

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_convex_frontier_disk_of_compact_with_open_interior (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {s : Set E} (hs : IsCompact s) (hcv : Convex ℝ s)
    (hne : (interior s).Nonempty) (hspace : K.space = frontier s)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F + 1)
    (p : frontier s) {a : Set E} (ha : IsCompact a) (has : a ⊆ frontier s)
    (hpa : (p : E) ∉ a) :
    ∃ d q : Set E, IsFinitePLBallPair F d q ∧ d ⊆ frontier s ∧
      a ⊆ d \ q ∧ (p : E) ∉ d ∧
      IsOpen ((Subtype.val : frontier s → E) ⁻¹' (d \ q)) := by
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let ι := Fin (Module.finrank ℝ E)
  let c : E ≃L[ℝ] (ι → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [ι])
  obtain ⟨e, he, hep⟩ := K.exists_finitePL_convex_frontier_cube_pole hK hs hcv hne hspace c p
  have hecopy := he
  obtain ⟨f, hf, heval⟩ := hecopy
  obtain ⟨g, hg, hgval⟩ := he.symm
  let T := frontier (Metric.closedBall (0 : ι → ℝ) 1)
  have hfmap (x : E) (hx : x ∈ frontier s) : f x ∈ T := by
    rw [← heval ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).property
  have hgmap (y : ι → ℝ) (hy : y ∈ T) : g y ∈ frontier s := by
    rw [← hgval ⟨y, hy⟩]
    exact (e.symm ⟨y, hy⟩).property
  have hgf : LeftInvOn g f (frontier s) := by
    intro x hx
    rw [← heval ⟨x, hx⟩, ← hgval, e.symm_apply_apply]
  have hfg : LeftInvOn f g T := by
    intro y hy
    rw [← hgval ⟨y, hy⟩, ← heval, e.apply_symm_apply]
  have haf : IsCompact (f '' a) := ha.image_of_continuousOn (hf.continuousOn.mono has)
  have hafsub : f '' a ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact hfmap x (has hx)
  have hfp : f p = fun _ => 1 := (heval p).symm.trans hep
  have hpf : (fun _ : ι => (1 : ℝ)) ∉ f '' a := by
    rintro ⟨x, hx, hfx⟩
    have hxp := hgf.injOn (has hx) p.property (hfx.trans hfp.symm)
    exact hpa (hxp ▸ hx)
  obtain ⟨d, q, hd, hdT, had, hpd, hopen⟩ :=
    exists_cube_frontier_disk_of_compact_with_open_interior haf hafsub hpf
      (F := F) (by simpa [ι] using hdim)
  have hdcopy := hd
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJd, _⟩, _⟩, _⟩ := hdcopy
  have hgD : FinitePiecewiseAffineOn g d := by
    rw [← hJd]
    exact hg.restrict J hJ (hJd.subset.trans hdT)
  refine ⟨g '' d, g '' q, hd.image hgD (hfg.injOn.mono hdT), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hgmap y (hdT hy)
  · intro x hx
    have hfx := had (mem_image_of_mem f hx)
    refine ⟨⟨f x, hfx.1, hgf (has hx)⟩, ?_⟩
    rintro ⟨y, hy, hyx⟩
    have hfy : f x = y := by rw [← hyx, hfg (hdT (hd.1 hy))]
    exact hfx.2 (hfy.symm ▸ hy)
  · rintro ⟨y, hy, hyp⟩
    have hfy : y = fun _ => 1 := by rw [← hfg (hdT hy), hyp, hfp]
    exact hpd (hfy ▸ hy)
  · have hmem (b : Set (ι → ℝ)) (hb : b ⊆ T) (x : frontier s) :
        (x : E) ∈ g '' b ↔ (e x : ι → ℝ) ∈ b := by
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hexy : (e x : ι → ℝ) = y := by
          rw [heval, ← hyx, hfg (hb hy)]
        rwa [hexy]
      · intro hx
        refine ⟨e x, hx, ?_⟩
        rw [← hgval (e x), e.symm_apply_apply]
    have heq : (Subtype.val : frontier s → E) ⁻¹' (g '' d \ g '' q) =
        e ⁻¹' ((Subtype.val : T → (ι → ℝ)) ⁻¹' (d \ q)) := by
      ext x
      change ((x : E) ∈ g '' d ∧ (x : E) ∉ g '' q) ↔
        ((e x : ι → ℝ) ∈ d ∧ (e x : ι → ℝ) ∉ q)
      rw [hmem d hdT, hmem q (hd.1.trans hdT)]
    rw [heq]
    exact hopen.preimage e.continuous

theorem exists_convex_frontier_disk_of_compact (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {s : Set E} (hs : IsCompact s) (hcv : Convex ℝ s)
    (hne : (interior s).Nonempty) (hspace : K.space = frontier s)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F + 1)
    (p : frontier s) {a : Set E} (ha : IsCompact a) (has : a ⊆ frontier s)
    (hpa : (p : E) ∉ a) :
    ∃ d q : Set E, IsFinitePLBallPair F d q ∧ d ⊆ frontier s ∧
      a ⊆ d \ q ∧ (p : E) ∉ d := by
  obtain ⟨d, q, hd, hds, had, hpd, _⟩ :=
    K.exists_convex_frontier_disk_of_compact_with_open_interior hK hs hcv hne hspace
      hdim p ha has hpa
  exact ⟨d, q, hd, hds, had, hpd⟩

end Geometry.SimplicialComplex
