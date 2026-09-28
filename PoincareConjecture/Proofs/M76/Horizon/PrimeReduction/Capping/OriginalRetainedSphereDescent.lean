import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.SphereModelCap
import PoincareConjecture.Proofs.M76.Wall.OriginalFinitePLSphereImage
import PoincareConjecture.Proofs.M76.RelativeApproximation.ModelInverse









set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_sphere_of_retained_model
    {E G X ι α : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {Q R : Set X}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (H : Q ≃ₜ K.space) (F : X → E) (hRQ : R ⊆ Q)
    (hHF : ∀ x : Q, (H x : E) = F x)
    (hproj : ∀ x ∈ Q, ∃ (i : ι) (V : Set X) (a : E →ᴬ[ℝ] V3),
      IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ F) (e i) V)
    {W : Set (E × G)} (atlas : α → OpenPartialHomeomorph W V3)
    (hrep : ∀ i, ∃ g : V3 → E × G, FinitePiecewiseAffineOn g (closedBall (0 : V3) 1) ∧
      (atlas i).target ⊆ interior (closedBall (0 : V3) 1) ∧
      ∀ y ∈ (atlas i).target, ((atlas i).symm y : E × G) = g y)
    {S : Set W} (s : ChartwisePLSphere atlas S)
    (hret : S ⊆ (Subtype.val : W → E × G) ⁻¹' (fun x => (F x,(0 : G))) '' R) :
    ∃ T : Set X, Nonempty (ChartwisePLSphere e T) ∧ T ⊆ R ∧
      (fun x => (F x,(0 : G))) '' T = (Subtype.val : W → E × G) '' S := by
  classical
  let p : W → E := fun x => (x : E × G).1
  have hp (i : α) : LocallyPiecewiseAffineOn (p ∘ (atlas i).symm) (atlas i).target := by
    obtain ⟨g,hg,hgt,hgv⟩ := hrep i
    let a : E × G →ᴬ[ℝ] E := (ContinuousLinearMap.fst ℝ E G).toContinuousAffineMap
    apply ((hg.postcomp a).locallyPiecewiseAffineOn_of_subset_interior (atlas i).open_target hgt).congr
    intro y hy
    change (g y).1 = ((atlas i).symm y : E × G).1
    exact congrArg Prod.fst (hgv y hy).symm
  have hzero (x : W) (hx : x ∈ S) : (x : E × G).2 = 0 := by
    obtain ⟨y,_,hy⟩ := hret hx
    exact (congrArg Prod.snd hy).symm
  have hpi : InjOn p S := by
    intro x hx y hy hxy
    exact Subtype.ext (Prod.ext hxy ((hzero x hx).trans (hzero y hy).symm))
  have hNK : p '' S ⊆ K.space := by
    rintro z ⟨y,hy,rfl⟩
    obtain ⟨x,hx,hxy⟩ := hret hy
    have hval : p y = F x := (congrArg Prod.fst hxy).symm
    rw [hval,←hHF ⟨x,hRQ hx⟩]
    exact (H ⟨x,hRQ hx⟩).property
  obtain ⟨A,hA,_⟩ := s.exists_finitePL_model_parametrization p hp hpi rfl
  obtain ⟨z,hz⟩ := (NormedSpace.sphere_nonempty.mpr zero_le_one :
    (sphere (0 : V3) 1).Nonempty)
  let y : S := s.parametrization ⟨z,hz⟩
  let x₀ : Q := H.symm ⟨p y,hNK ⟨y,y.property,rfl⟩⟩
  obtain ⟨g,_,hgv,hg⟩ := exists_polyhedral_PL_model_inverse e K hK H F subset_rfl x₀ hHF hproj
  have hgi : InjOn (fun z => (g z : X)) K.space := by
    intro x hx y hy hxy
    have hEq : H.symm ⟨x,hx⟩ = H.symm ⟨y,hy⟩ :=
      Subtype.ext ((hgv ⟨x,hx⟩).symm.trans (hxy.trans (hgv ⟨y,hy⟩)))
    exact congrArg Subtype.val (H.symm.injective hEq)
  have hreal (x : Q) : (g (F x) : X) = x := by
    rw [←hHF x,hgv (H x),H.symm_apply_apply]
  have hFg (z : E) (hz : z ∈ K.space) : F (g z) = z := by
    rw [hgv ⟨z,hz⟩,←hHF (H.symm ⟨z,hz⟩),H.apply_symm_apply]
  let T := (fun z => (g z : X)) '' (p '' S)
  have hT : T ⊆ R := by
    rintro _ ⟨z,⟨x,hx,rfl⟩,rfl⟩
    obtain ⟨v,hv,hvx⟩ := hret hx
    have hpx : p x = F v := (congrArg Prod.fst hvx).symm
    change (g (p x) : X) ∈ R
    rw [hpx,hreal ⟨v,hRQ hv⟩]
    exact hv
  refine ⟨T,exists_chartwisePLSphere_image K hg hgi hNK A.symm hA.symm,hT,?_⟩
  ext v
  constructor
  · rintro ⟨_,⟨z,⟨x,hx,rfl⟩,rfl⟩,rfl⟩
    refine ⟨x,hx,?_⟩
    change (x : E × G) = (F (g (p x)),0)
    rw [hFg _ (hNK ⟨x,hx,rfl⟩)]
    exact Prod.ext rfl (hzero x hx)
  · rintro ⟨x,hx,rfl⟩
    refine ⟨g (p x),⟨p x,⟨x,hx,rfl⟩,rfl⟩,?_⟩
    change (F (g (p x)),(0 : G)) = (x : E × G)
    rw [hFg _ (hNK ⟨x,hx,rfl⟩)]
    exact Prod.ext rfl (hzero x hx).symm

end PoincareConjecture.M76
