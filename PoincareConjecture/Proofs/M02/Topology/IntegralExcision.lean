import PoincareConjecture.Proofs.M02.Topology.IntegralChainSupport
import PoincareConjecture.Proofs.M02.Topology.IntegralSmallRelativeChains









set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

universe u

namespace PoincareConjecture.Proofs.M02.Topology

private theorem integralCokernelMap_isIso
    {K₁ K₂ L₁ L₂ : ChainComplex (ModuleCat.{u} Int) Nat}
    (f : K₁ ⟶ K₂) (g : L₁ ⟶ L₂) (p : K₁ ⟶ L₁) (q : K₂ ⟶ L₂)
    (w : f ≫ q = p ≫ g)
    (hspan : ∀ (n : Nat) (d : L₂.X n),
      ∃ (b : K₂.X n) (c : L₁.X n), q.f n b + g.f n c = d)
    (hinter : ∀ (n : Nat) (b : K₂.X n),
      q.f n b ∈ LinearMap.range (g.f n).hom → b ∈ LinearMap.range (f.f n).hom) :
    IsIso (cokernel.map f g p q w) := by
  let r := cokernel.map f g p q w
  let πf := cokernel.π f
  let πg := cokernel.π g
  have hπ (n : Nat) : πf.f n ≫ r.f n = q.f n ≫ πg.f n :=
    congrArg (fun k => k.f n) (cokernel.π_desc f (q ≫ cokernel.π g) _)
  have hker {C D : ChainComplex (ModuleCat.{u} Int) Nat} (k : C ⟶ D)
      (n : Nat) (d : D.X n) :
      (cokernel.π k).f n d = 0 ↔ d ∈ LinearMap.range (k.f n).hom := by
    constructor
    · intro hd
      exact (ShortComplex.moduleCat_exact_iff _).mp
        ((ShortComplex.cokernelSequence_exact k).map
          (HomologicalComplex.eval (ModuleCat.{u} Int) (ComplexShape.down Nat) n)) d hd
    · rintro ⟨c, rfl⟩
      exact congrArg (fun h => h.f n c) (cokernel.condition k)
  have hdeg (n : Nat) : IsIso (r.f n) := by
    have hinj : Function.Injective (r.f n) := by
      apply (injective_iff_map_eq_zero _).mpr
      intro y hy
      obtain ⟨b, hb⟩ := (ModuleCat.epi_iff_surjective (πf.f n)).mp inferInstance y
      have hqb : πg.f n (q.f n b) = 0 := by
        have he := congrArg (fun k => k b) (hπ n)
        change r.f n (πf.f n b) = πg.f n (q.f n b) at he
        exact he.symm.trans (by rw [hb]; exact hy)
      exact hb.symm.trans ((hker f n b).mpr (hinter n b ((hker g n _).mp hqb)))
    have hsurj : Function.Surjective (r.f n) := by
      intro y
      obtain ⟨d, hd⟩ := (ModuleCat.epi_iff_surjective (πg.f n)).mp inferInstance y
      obtain ⟨b, c, hbc⟩ := hspan n d
      refine ⟨πf.f n b, ?_⟩
      calc
        r.f n (πf.f n b) = πg.f n (q.f n b) :=
          congrArg (fun k => k b) (hπ n)
        _ = πg.f n (q.f n b + g.f n c) := by
          rw [map_add, (hker g n _).mpr ⟨c, rfl⟩, add_zero]
        _ = y := by rw [hbc, hd]
    let : Mono (r.f n) := (ModuleCat.mono_iff_injective _).mpr hinj
    let : Epi (r.f n) := (ModuleCat.epi_iff_surjective _).mpr hsurj
    exact isIso_of_mono_of_epi _
  let := hdeg
  exact HomologicalComplex.Hom.isIso_of_components _

variable {X : Type u} [TopologicalSpace X]



theorem integral_open_cover_excision
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = Set.univ) (n : Nat) :
    IsIso (HomologicalComplex.homologyMap
      (integralRelativeMap (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
        (A := (Subtype.val : B → X) ⁻¹' A) (B := A) (fun _ hb => hb)) n) := by
  let U : Bool → Set X := fun b => if b then A else B
  let UA : Bool → Set A := fun b => (Subtype.val : A → X) ⁻¹' U b
  let UB : Bool → Set B := fun b => (Subtype.val : B → X) ⁻¹' U b
  let AB : Set B := (Subtype.val : B → X) ⁻¹' A
  have hUA : UA true = Set.univ := by
    ext a
    exact ⟨fun _ => Set.mem_univ _, fun _ => a.property⟩
  have hUB : UB false = Set.univ := by
    ext b
    exact ⟨fun _ => Set.mem_univ _, fun _ => b.property⟩
  let jA := integralSmallChainInclusion UA
  let jB := integralSmallChainInclusion UB
  let j := integralSmallChainInclusion U
  let : IsIso jA := integralSmallChainInclusion_isIso_of_univ UA true hUA
  let : IsIso jB := integralSmallChainInclusion_isIso_of_univ UB false hUB
  let f := integralSubspaceChains AB
  let g := integralSmallSubspaceChains U A
  let q := inv jB ≫ integralSmallSubspaceChains U B
  let a : C(AB, A) := ⟨fun x => ⟨x.val.val, x.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let t := integralChainsFunctor.map (TopCat.ofHom a)
  let p := t ≫ inv jA
  have hg : g ≫ j = jA ≫ integralSubspaceChains A :=
    integralSmallSubspaceChains_inclusion U A
  have hq : q ≫ j = integralSubspaceChains B := by
    dsimp only [q]
    rw [Category.assoc, integralSmallSubspaceChains_inclusion U B,
      ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have ht : f ≫ integralSubspaceChains B = t ≫ integralSubspaceChains A := by
    change integralChainsFunctor.map _ ≫ integralChainsFunctor.map _ =
      integralChainsFunctor.map _ ≫ integralChainsFunctor.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  have w : f ≫ q = p ≫ g := by
    let : Mono j := integralSmallChainInclusion_mono U
    apply (cancel_mono j).mp
    rw [Category.assoc, hq, Category.assoc, hg]
    dsimp only [p]
    rw [Category.assoc, ← Category.assoc (inv jA), IsIso.inv_hom_id,
      Category.id_comp, ht]
  let r := cokernel.map f g p q w
  have hqval (m : Nat) (b : (integralChains B).X m) :
      j.f m (q.f m b) = (integralSubspaceChains B).f m b :=
    congrArg (fun k => k.f m b) hq
  have hgval (m : Nat) (a' : (integralSmallChainComplex UA).X m) :
      j.f m (g.f m a') = (integralSubspaceChains A).f m (jA.f m a') :=
    congrArg (fun k => k.f m a') hg
  have hspan (m : Nat) (d : (integralSmallChainComplex U).X m) :
      ∃ (b : (integralChains B).X m) (c : (integralSmallChainComplex UA).X m),
        q.f m b + g.f m c = d := by
    have hd : d.val ∈ LinearMap.range ((integralSubspaceChains A).f m).hom ⊔
        LinearMap.range ((integralSubspaceChains B).f m).hom := by
      rw [← integralSmallChains_two_eq_sup A B m]
      exact d.property
    obtain ⟨x, ⟨a', rfl⟩, y, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.mp hd
    refine ⟨b, (inv jA).f m a', ?_⟩
    apply Subtype.ext
    change j.f m (q.f m b) + j.f m (g.f m ((inv jA).f m a')) = d.val
    rw [hqval, hgval]
    have hja : jA.f m ((inv jA).f m a') = a' :=
      congrArg (fun k => k.f m a') (IsIso.inv_hom_id jA)
    rw [hja]
    exact (add_comm _ _).trans hab
  have hinter (m : Nat) (b : (integralChains B).X m)
      (hb : q.f m b ∈ LinearMap.range (g.f m).hom) :
      b ∈ LinearMap.range (f.f m).hom := by
    apply (integralSubspaceChains_range_preimage A B m b).mp
    obtain ⟨a', ha'⟩ := hb
    refine ⟨jA.f m a', ?_⟩
    have he := congrArg (j.f m) ha'
    rw [hgval, hqval] at he
    exact he
  let : IsIso r := integralCokernelMap_isIso f g p q w hspan hinter
  have hU : ∀ b, IsOpen (U b) := by
    intro b
    cases b
    · exact hB
    · exact hA
  have hcoverU : (⋃ b, U b) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    have hx : x ∈ A ∪ B := by rw [hcover]; exact Set.mem_univ _
    rcases hx with hx | hx
    · exact Set.mem_iUnion.mpr ⟨true, hx⟩
    · exact Set.mem_iUnion.mpr ⟨false, hx⟩
  let c := integralSmallRelativeComparison U A
  have hr : integralRelativeProjection AB ≫ r = q ≫ integralSmallRelativeProjection U A :=
    cokernel.π_desc _ _ _
  have hfactor : r ≫ c = integralRelativeMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
      (A := AB) (B := A) (fun _ hb => hb) := by
    apply (cancel_epi (integralRelativeProjection AB)).mp
    rw [← Category.assoc, hr, Category.assoc,
      integralSmallRelativeComparison_projection, ← Category.assoc, hq]
    exact (integralRelativeMap_projection
      (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X))
      (A := AB) (B := A) (fun _ hb => hb)).symm
  let : IsIso (HomologicalComplex.homologyMap c n) :=
    integralSmallRelativeComparison_homology_isIso U hU hcoverU A n
  rw [← hfactor, HomologicalComplex.homologyMap_comp]
  infer_instance

end PoincareConjecture.Proofs.M02.Topology
