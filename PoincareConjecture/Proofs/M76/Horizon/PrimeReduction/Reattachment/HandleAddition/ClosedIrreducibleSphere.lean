import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.CollarCompressionConfinement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.SphereModelCap
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFiniteModelBallImages
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFinitePLBallImage
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLIrreducibility

set_option autoImplicit false
open Set Geometry Metric
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "Q3" => sphere (0 : V3) 1

theorem IsPLIrreducible.exists_ball_of_sphere_subset
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X}
    (hI : IsPLIrreducible e R) (hR : IsCompact R)
    (s : ChartwisePLSphere e S) (hSR : S ⊆ R) :
    ∃ B : Set X, B ⊆ R ∧ Nonempty (ChartwisePLBall e B S) := by
  classical
  obtain ⟨q,hq⟩ := NormedSpace.sphere_nonempty (E := V3) (x := 0) |>.mpr (show (0 : ℝ) ≤ 1 by norm_num)
  obtain ⟨M⟩ := hI.1.nonempty_original_finite_collar_model hR
    ⟨s.parametrization ⟨q,hq⟩,hSR (s.parametrization ⟨q,hq⟩).property⟩
  let F := M.vertices → ℝ × V3
  let g : F → X := fun z => M.inverse z
  have hg : InjOn g M.complex.space := by
    intro x hx y hy hxy
    have hh : M.homeomorph.symm ⟨x,hx⟩ = M.homeomorph.symm ⟨y,hy⟩ :=
      Subtype.ext ((M.inverse_eq ⟨x,hx⟩).symm.trans (hxy.trans (M.inverse_eq ⟨y,hy⟩)))
    exact congrArg Subtype.val (M.homeomorph.symm.injective hh)
  have hfg (z : F) (hz : z ∈ M.complex.space) : M.coordinates (g z) = z := by
    change M.coordinates (M.inverse z) = z
    rw [M.inverse_eq ⟨z,hz⟩,←M.homeomorph_eq,M.homeomorph.apply_symm_apply]
  obtain ⟨D,H,hH,hDK,hDA,_,hconfine⟩ := M.exists_inward_compression_with_ball_confinement
  obtain ⟨a,ha,haval⟩ := hH
  obtain ⟨a',ha',ha'val⟩ := (show H.IsFinitePL from ⟨a,ha,haval⟩).symm
  have haD (z : F) (hz : z ∈ M.complex.space) : a z ∈ D := by
    rw [←haval ⟨z,hz⟩]; exact (H ⟨z,hz⟩).property
  have haK (z : F) (hz : z ∈ D) : a' z ∈ M.complex.space := by
    rw [←ha'val ⟨z,hz⟩]; exact (H.symm ⟨z,hz⟩).property
  have hainj : InjOn a M.complex.space := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((haval ⟨x,hx⟩).trans (hxy.trans (haval ⟨y,hy⟩).symm))))
  have ha'inj : InjOn a' D := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.symm.injective (Subtype.ext
      ((ha'val ⟨x,hx⟩).trans (hxy.trans (ha'val ⟨y,hy⟩).symm))))
  have hcancel (z : F) (hz : z ∈ M.complex.space) : a' (a z) = z := by
    rw [←haval ⟨z,hz⟩,←ha'val,H.symm_apply_apply]
  have hcore : g '' D ⊆ interior R := by
    rintro _ ⟨z,hz,rfl⟩
    apply (mem_interior_iff_notMem_frontier (M.inverse z).property).mpr
    exact fun hn => disjoint_left.mp hDA hz ((M.boundary_eq z (hDK hz)).mp hn)
  obtain ⟨Q,hQ,hQval⟩ := s.exists_finitePL_model_parametrization M.coordinates
    M.coordinates_pl (M.coordinates_injective.mono hSR) rfl
  obtain ⟨v,hv,hvval⟩ := hQ
  have hvK (x : V3) (hx : x ∈ Q3) : v x ∈ M.complex.space := by
    rw [←hvval ⟨x,hx⟩]
    obtain ⟨y,hy,heq⟩ := (Q ⟨x,hx⟩).property
    exact heq ▸ M.coordinates_mapsTo (hSR hy)
  have hav : FinitePiecewiseAffineOn (a ∘ v) Q3 := ha.comp hv hvK
  have havD : MapsTo (a ∘ v) Q3 D := fun x hx => haD _ (hvK x hx)
  have hvi : InjOn v Q3 := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (Q.injective (Subtype.ext
      ((hvval ⟨x,hx⟩).trans (hxy.trans (hvval ⟨y,hy⟩).symm))))
  have havinj : InjOn (a ∘ v) Q3 := fun x hx y hy h =>
    hvi hx hy (hainj (hvK x hx) (hvK y hy) h)
  let k := g ∘ (a ∘ v)
  have hkPL : PolyhedralPLInCharts e k Q3 := by
    obtain ⟨K,hK,hKs,hfaces⟩ := hav
    rw [←hKs]
    exact M.inverse_pl.comp_finitePiecewiseAffineOn K hK ⟨K,hK,rfl,hfaces⟩
      (fun x hx => hDK (havD (hKs.subset hx)))
  have hki : InjOn k Q3 := fun x hx y hy h => havinj hx hy
    (hg (hDK (havD hx)) (hDK (havD hy)) h)
  let K : Q3 ≃ₜ k '' Q3 := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn k Q3 hki) (hkPL.continuousOn.domRestrict.subtype_mk _)
  let s' : ChartwisePLSphere e (k '' Q3) :=
    ⟨K,k,fun _ => rfl,hkPL⟩
  have hS' : k '' Q3 ⊆ g '' D := by
    rintro _ ⟨x,hx,rfl⟩; exact ⟨a (v x),havD hx,rfl⟩
  obtain ⟨B,hBR,⟨b⟩⟩ := hI.2 (k '' Q3) (hS'.trans hcore) ⟨s'⟩
  have hBD := hconfine B (k '' Q3) b hBR hS'
  have hBC : M.coordinates '' B ⊆ D := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨z,hz,rfl⟩ := hBD hx
    rwa [hfg z (hDK hz)]
  have hb := b.finitePLBallPair_image hBR M.coordinates M.coordinates_pl M.coordinates_injective
  have hb' := hb.image_of_subset ha' hBC ha'inj
  have hback : a' '' (M.coordinates '' B) ⊆ M.complex.space := by
    rintro _ ⟨x,hx,rfl⟩; exact haK x (hBC hx)
  obtain ⟨back⟩ := exists_chartwisePLBall_image hb' (ContinuousLinearEquiv.refl ℝ V3)
    M.inverse_pl hback hg
  have hboundary : g '' (a' '' (M.coordinates '' (k '' Q3))) = S := by
    have hpoint (x : V3) (hx : x ∈ Q3) : g (a' (M.coordinates (k x))) = s.map x := by
      change g (a' (M.coordinates (g (a (v x))))) = _
      rw [hfg (a (v x)) (hDK (havD hx)),hcancel (v x) (hvK x hx),←hvval ⟨x,hx⟩,hQval]
      exact M.inverse_coordinates _ (hSR (by rw [s.map_eq ⟨x,hx⟩]; exact (s.parametrization ⟨x,hx⟩).property))
    apply Subset.antisymm
    · rintro _ ⟨_,⟨_,⟨_,⟨x,hx,rfl⟩,rfl⟩,rfl⟩,rfl⟩
      rw [hpoint x hx,s.map_eq ⟨x,hx⟩]
      exact (s.parametrization ⟨x,hx⟩).property
    · intro x hx
      obtain ⟨z,hz⟩ := s.parametrization.surjective ⟨x,hx⟩
      refine ⟨_,⟨_,⟨_,⟨z,z.property,rfl⟩,rfl⟩,rfl⟩,?_⟩
      exact (hpoint z z.property).trans ((s.map_eq z).trans (congrArg Subtype.val hz))
  rw [hboundary] at back
  refine ⟨g '' (a' '' (M.coordinates '' B)),?_,⟨back⟩⟩
  rintro _ ⟨z,hz,rfl⟩
  exact (M.inverse z).property

end PoincareConjecture.M76
