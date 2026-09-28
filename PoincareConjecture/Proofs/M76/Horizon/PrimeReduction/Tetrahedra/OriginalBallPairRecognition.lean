import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalSurfaceComplex
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem isFinitePLBallPair_of_original_parametrization
    {X E F M ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup M] [NormedSpace ℝ M]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    {C R : Set E} (hCK : C ⊆ K.space) (hRK : R ⊆ K.space)
    {d q : Set F} (hd : IsFinitePLBallPair M d q)
    {p : F → X} (hp : PolyhedralPLInCharts e p d) (hpi : InjOn p d)
    (hcarrier : p '' d = g '' C) (hrim : p '' q = g '' R) :
    IsFinitePLBallPair M C R := by
  classical
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  let H := hg.continuousOn.domRestrict.isClosedEmbedding
    (fun x y h => Subtype.ext (hgi x.property y.property h)) |>.isEmbedding.toHomeomorph
  let pr : K.space ≃ₜ (g '' K.space) :=
    H.trans (Homeomorph.setCongr (image_eq_range g K.space).symm)
  have hpK (x : F) (hx : x ∈ d) : p x ∈ g '' K.space :=
    image_mono hCK (hcarrier.subset ⟨x,hx,rfl⟩)
  let f : F → E := fun x => if hx : x ∈ d then pr.symm ⟨p x,hpK x hx⟩ else 0
  have hfval (x : d) : f x = (pr.symm ⟨p x,hpK x x.property⟩ : E) := by
    simp only [f,dif_pos x.property]
  have hfK : MapsTo f d K.space := by
    intro x hx
    rw [hfval ⟨x,hx⟩]
    exact (pr.symm ⟨p x,hpK x hx⟩).property
  have hvalue (x : F) (hx : x ∈ d) : g (f x) = p x := by
    rw [hfval ⟨x,hx⟩]
    exact congrArg Subtype.val (pr.apply_symm_apply ⟨p x,hpK x hx⟩)
  have hfc : ContinuousOn f d := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc := continuous_subtype_val.comp (pr.symm.continuous.comp
      (hp.continuousOn.domRestrict.subtype_mk (fun x => hpK x x.property)))
    convert hc using 1
    funext x
    exact hfval x
  have hcopy := hd
  obtain ⟨_,_,_,_,_,_,⟨_,⟨A,hA,hAd,_⟩,_⟩,_⟩ := hcopy
  have hf : FinitePiecewiseAffineOn f d := by
    rw [←hAd]
    exact hg.finitePiecewiseAffineOn_lift he hgi A hA
      (hfc.mono hAd.subset) (fun x hx => hfK (hAd.subset hx))
      ((hAd.symm ▸ hp).congr (fun x hx => (hvalue x (hAd.subset hx)).symm))
  have hfi : InjOn f d := by
    intro x hx y hy hxy
    apply hpi hx hy
    rw [←hvalue x hx,←hvalue y hy,hxy]
  have himage {a : Set F} {b : Set E} (had : a ⊆ d) (hbK : b ⊆ K.space)
      (hab : p '' a = g '' b) : f '' a = b := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨y,hy,hyx⟩ := hab.subset ⟨x,hx,rfl⟩
      have heq := hgi (hfK (had hx)) (hbK hy) ((hvalue x (had hx)).trans hyx.symm)
      exact heq.symm ▸ hy
    · intro y hy
      obtain ⟨x,hx,hxy⟩ := hab.symm.subset ⟨y,hy,rfl⟩
      exact ⟨x,hx,hgi (hfK (had hx)) (hbK hy) ((hvalue x (had hx)).trans hxy)⟩
  simpa only [himage subset_rfl hCK hcarrier,himage hd.1 hRK hrim] using hd.image hf hfi

end PoincareConjecture.M76
