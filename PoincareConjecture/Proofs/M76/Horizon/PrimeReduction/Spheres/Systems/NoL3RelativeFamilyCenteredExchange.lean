import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RelativeProductCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3ComponentReassembly
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.LocalCollarCutExtension
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RelativeCollarEndpointFrontiers
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SelectedOriginalCutDomain








set_option autoImplicit false
open Set Metric Geometry TriangularRoofModel
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Base" => frontier (halfBall 1)
local notation "I" => Icc (0 : ℝ) 1

theorem HasNoPuncturedSphereComponents.exists_fixed_relative_family_centered_exchange
    {X E ι κ : Type*} [MetricSpace X] [Finite κ] [DecidableEq κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {R U Snew : Set X}
    (O S : κ → Set X) (W : ∀ k, (S k × unitInterval) ≃ₜ closure (O k))
    (hR : IsCompact R) (he : PLDomain e R)
    (hQPL : PLDomain e (R \ ⋃ k, O k))
    (hO : ∀ k, IsOpen (O k)) (hOR : ∀ k, closure (O k) ⊆ interior R)
    (hdis : Pairwise fun k l => Disjoint (closure (O k)) (closure (O l)))
    (hWopen : ∀ k z, (W k z : X) ∈ O k ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hWcenter : ∀ k z, (W k z : X) ∈ S k ↔ (z.2 : ℝ) = 1/2)
    (hSC : ∀ k, S k ⊆ closure (O k)) (sS : ∀ k, ChartwisePLSphere e (S k))
    (B : κ × Bool → Set X) (sB : ∀ j, ChartwisePLSphere e (B j))
    (hBdis : Pairwise fun j l => Disjoint (B j) (B l))
    (hBsub : ∀ j, B j ⊆ closure (O j.1))
    (hBfront : frontier (R \ ⋃ k, O k) = frontier R ∪ ⋃ j, B j)
    (i : κ) (a : X)
    (hC : IsCompact (connectedComponentIn (R \ ⋃ k : {k : κ // k ≠ i}, O k.val) a))
    (hCPL : PLDomain e (connectedComponentIn (R \ ⋃ k : {k : κ // k ≠ i}, O k.val) a))
    (caps : ChartwisePLSphere e Snew)
    (WU : U ≃ₜ (Base ×ˢ I : Set (P3 × ℝ))) (σ : P3 × ℝ → X)
    (hσ : PolyhedralPLInCharts e σ (Base ×ˢ I))
    (hσval : ∀ z : (Base ×ˢ I : Set (P3 × ℝ)), σ z = (WU.symm z : X))
    (b : Bool) (hSU : Snew ⊆ U)
    (hUC : U ⊆ interior (connectedComponentIn (R \ ⋃ k : {k : κ // k ≠ i}, O k.val) a))
    (hmark : ∀ x : U, (x : X) ∈ Snew ↔ (WU x : P3 × ℝ).2 = if b then (1 : ℝ) else 0)
    (hno : HasNoPuncturedSphereComponents e f
      ((R \ ⋃ k : {k : κ // k ≠ i}, O k.val) \ interior U))
    (hnoC : HasNoPuncturedSphereComponents e f
      (connectedComponentIn (R \ ⋃ k : {k : κ // k ≠ i}, O k.val) a \ interior U))
    (L : SimplicialComplex ℝ E) (g : E → X)
    (hf : ∀ j, LocallyPiecewiseAffineOn (f ∘ (e j).symm) (e j).target)
    (hg : PolyhedralPLInCharts e g L.space) (hgi : InjOn g L.space)
    (hreal : ∀ x ∈ R, f x ∈ L.space ∧ g (f x) = x) :
    ∃ (Oc : Set X) (Hc : (Snew × unitInterval) ≃ₜ closure Oc),
      let O' := Function.update O i Oc
      let S' := Function.update S i Snew
      ∃ (sS' : ∀ k, ChartwisePLSphere e (S' k))
        (W' : ∀ k, (S' k × unitInterval) ≃ₜ closure (O' k))
        (G : κ × Bool → Set X) (_sG : ∀ j, ChartwisePLSphere e (G j)),
        IsOpen Oc ∧ closure Oc ⊆ interior
          (connectedComponentIn (R \ ⋃ k : {k : κ // k ≠ i}, O k.val) a) ∧
        (∀ z, (Hc z : X) ∈ Oc ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
        (∀ z, (Hc z : X) ∈ Snew ↔ (z.2 : ℝ) = 1/2) ∧
        (∀ k, IsOpen (O' k) ∧ closure (O' k) ⊆ interior R) ∧
        Pairwise (fun k l => Disjoint (closure (O' k)) (closure (O' l))) ∧
        (∀ k z, (W' k z : X) ∈ O' k ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
        (∀ k z, (W' k z : X) ∈ S' k ↔ (z.2 : ℝ) = 1/2) ∧
        (∀ k, S' k ⊆ closure (O' k)) ∧
        (∀ k (hk : k ≠ i) (z : S' k × unitInterval),
          (W' k z : X) = (W k (⟨z.1,(by simpa [S',Function.update_of_ne hk] using z.1.property)⟩,z.2) : X)) ∧
        Pairwise (fun k l => Disjoint (S' k) (S' l)) ∧
        IsCompact (R \ ⋃ k, O' k) ∧ PLDomain e (R \ ⋃ k, O' k) ∧
        HasNoPuncturedSphereComponents e f (R \ ⋃ k, O' k) ∧
        Pairwise (fun j l => Disjoint (G j) (G l)) ∧
        (∀ j, G j ⊆ closure (O' j.1)) ∧
        frontier (R \ ⋃ k, O' k) = frontier R ∪ ⋃ j, G j := by
  classical
  let A := R \ ⋃ k : {k : κ // k ≠ i}, O k.val
  let C := connectedComponentIn A a
  have hCA : C ⊆ A := connectedComponentIn_subset A a
  have hCR : C ⊆ R := hCA.trans inter_subset_left
  obtain ⟨c,ε,hc,hci,hzero,hε,hεsmall,hsmall,hopen,hnoNew,D,sD,H,
      hcut,hcutPL,hDdis,hDsub,hOf,hDfront,hcl,hHO,hHS,hScl⟩ :=
    caps.exists_original_product_endpoint_relative_noL3_cut hC hCPL WU σ hσ hσval b hSU hUC
      hmark isOpen_univ (subset_univ _) hnoC L g hf hg hgi
      (fun x hx => hreal x (hCR hx))
  let Oc := c '' (sphere (0 : V3) 1 ×ˢ Ioo (-ε) ε)
  have hOc : IsOpen Oc := hopen ε hε le_rfl
  let Hc := (caps.parametrization.symm.prodCongr (Homeomorph.refl unitInterval)).trans H
  have hHcO (z : Snew × unitInterval) : (Hc z : X) ∈ Oc ↔
      (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1 := hHO (caps.parametrization.symm z.1,z.2)
  have hHcS (z : Snew × unitInterval) : (Hc z : X) ∈ Snew ↔
      (z.2 : ℝ) = 1/2 := hHS (caps.parametrization.symm z.1,z.2)
  let O' := Function.update O i Oc
  let S' := Function.update S i Snew
  let sS' : ∀ k, ChartwisePLSphere e (S' k) := fun k => by
    by_cases hk : k = i
    · subst k; simpa [S'] using caps
    · simpa [S',Function.update_of_ne hk] using sS k
  let W' : ∀ k, (S' k × unitInterval) ≃ₜ closure (O' k) := fun k => by
    by_cases hk : k = i
    · exact (((Homeomorph.setCongr (by simp [S',hk] : S' k = Snew)).prodCongr
        (Homeomorph.refl unitInterval)).trans Hc).trans
        (Homeomorph.setCongr (by simp [O',hk] : closure Oc = closure (O' k)))
    · exact (((Homeomorph.setCongr (by simp [S',hk] : S' k = S k)).prodCongr
        (Homeomorph.refl unitInterval)).trans (W k)).trans
        (Homeomorph.setCongr (by simp [O',hk] : closure (O k) = closure (O' k)))
  have hO' (k : κ) : IsOpen (O' k) ∧ closure (O' k) ⊆ interior R := by
    by_cases hk : k = i
    · subst k; simpa [O'] using (show IsOpen Oc ∧ closure Oc ⊆ interior R from
        ⟨hOc,hcl.trans (interior_mono hCR)⟩)
    · simpa [O',Function.update_of_ne hk] using (show IsOpen (O k) ∧ closure (O k) ⊆ interior R from ⟨hO k,hOR k⟩)
  have hsep (k : κ) (hk : k ≠ i) : Disjoint (closure Oc) (closure (O k)) := by
    apply disjoint_left.mpr
    intro x hxC hxk
    have hxAi := (interior_mono hCA) (hcl hxC)
    have hAi := (finite_collar_cut_geometry hR
      (fun j : {j : κ // j ≠ i} => hO j.val)
      (fun j : {j : κ // j ≠ i} => hOR j.val)
      (fun j l hjl => hdis (Subtype.val_injective.ne hjl))).2.1
    exact (hAi.subset hxAi).2 (mem_iUnion.mpr ⟨⟨k,hk⟩,hxk⟩)
  have hdis' : Pairwise fun k l => Disjoint (closure (O' k)) (closure (O' l)) := by
    intro k l hkl
    by_cases hk : k = i
    · subst k
      simpa [O',Function.update_of_ne (Ne.symm hkl)] using hsep l (Ne.symm hkl)
    · by_cases hl : l = i
      · subst l; simpa [O',Function.update_of_ne hk] using (hsep k hk).symm
      · simpa [O',Function.update_of_ne hk,Function.update_of_ne hl] using hdis hkl
  have hW'O : ∀ k z, (W' k z : X) ∈ O' k ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1 := by
    intro k z
    by_cases hk : k = i
    · subst k
      simpa [W',O',S',Homeomorph.setCongr,Equiv.setCongr,Equiv.subtypeEquivProp,
        Equiv.subtypeEquiv,Prod.map] using hHcO
        (⟨z.1,by simpa [S'] using z.1.property⟩,z.2)
    · simpa [W',O',S',hk,Homeomorph.setCongr,Equiv.setCongr,Equiv.subtypeEquivProp,
        Equiv.subtypeEquiv,Prod.map] using hWopen k
        (⟨z.1,by simpa [S',Function.update_of_ne hk] using z.1.property⟩,z.2)
  have hW'S : ∀ k z, (W' k z : X) ∈ S' k ↔ (z.2 : ℝ) = 1/2 := by
    intro k z
    by_cases hk : k = i
    · subst k
      simpa [W',O',S',Homeomorph.setCongr,Equiv.setCongr,Equiv.subtypeEquivProp,
        Equiv.subtypeEquiv,Prod.map] using hHcS
        (⟨z.1,by simpa [S'] using z.1.property⟩,z.2)
    · simpa [W',O',S',hk,Homeomorph.setCongr,Equiv.setCongr,Equiv.subtypeEquivProp,
        Equiv.subtypeEquiv,Prod.map] using hWcenter k
        (⟨z.1,by simpa [S',Function.update_of_ne hk] using z.1.property⟩,z.2)
  have hS'C (k : κ) : S' k ⊆ closure (O' k) := by
    by_cases hk : k = i
    · subst k; simpa [S',O'] using hScl
    · simpa [S',O',Function.update_of_ne hk] using hSC k
  have hQeq : R \ ⋃ k, O' k = A \ Oc := by
    ext x
    simp only [A,O',mem_sdiff,mem_iUnion,Subtype.exists,not_exists]
    constructor
    · rintro ⟨hxR,hxO⟩
      refine ⟨⟨hxR,fun k hk => ?_⟩,?_⟩
      · simpa [Function.update_of_ne hk] using hxO k
      · simpa using hxO i
    · rintro ⟨⟨hxR,hxO⟩,hxC⟩
      refine ⟨hxR,fun k => ?_⟩
      by_cases hk : k = i
      · subst k; simpa using hxC
      · simpa [Function.update_of_ne hk] using hxO k hk
  have hAc : IsCompact A := (finite_collar_cut_geometry hR
    (fun j : {j : κ // j ≠ i} => hO j.val)
    (fun j : {j : κ // j ≠ i} => hOR j.val)
    (fun j l hjl => hdis (Subtype.val_injective.ne hjl))).1
  have hAPL : PLDomain e A := hQPL.restore_one_disjoint_collar O hR hO hOR hdis i
  have hnewPL : PLDomain e (A \ Oc) :=
    hAPL.extension_of_local_collar_cut hAc hC hCA hOc hcl hcutPL
  have hnewNo : HasNoPuncturedSphereComponents e f (A \ Oc) :=
    hno.replace_component_cut (interior_subset.trans (hUC.trans interior_subset))
      (subset_closure.trans (hcl.trans interior_subset)) hnoNew
  let G : κ × Bool → Set X := fun j => if j.1 = i then D j.2 else B j
  let sG : ∀ j, ChartwisePLSphere e (G j) := fun j => by
    by_cases hj : j.1 = i
    · simpa [G,hj] using sD j.2
    · simpa [G,hj] using sB j
  have hGsub (j : κ × Bool) : G j ⊆ closure (O' j.1) := by
    by_cases hj : j.1 = i
    · simpa [G,O',hj] using hDsub j.2
    · simpa [G,O',Function.update_of_ne hj,hj] using hBsub j
  have hGdis : Pairwise fun j l => Disjoint (G j) (G l) := by
    rintro ⟨j,b⟩ ⟨k,d⟩ hjk
    by_cases hkey : j = k
    · subst k
      have hbd : b ≠ d := fun h => hjk (by simp [h])
      by_cases hji : j = i
      · simpa [G,hji] using hDdis hbd
      · simpa [G,hji] using hBdis hjk
    · exact (hdis' hkey).mono (hGsub (j,b)) (hGsub (k,d))
  have hOfront (k : κ) : frontier (O' k) = G (k,false) ∪ G (k,true) := by
    by_cases hk : k = i
    · subst k
      simpa [G,O'] using hOf
    · simpa [G,O',Function.update_of_ne hk,hk] using
        collar_frontier_eq_assigned_endpoints O hR hO hOR hdis B hBsub hBfront k
  have hGfront : frontier (R \ ⋃ k, O' k) = frontier R ∪ ⋃ j, G j := by
    rw [(finite_collar_cut_geometry hR (fun k => (hO' k).1)
      (fun k => (hO' k).2) hdis').2.2.1]
    congr 1
    simp_rw [hOfront]
    ext x
    simp only [mem_iUnion,mem_union,Prod.exists,Bool.exists_bool]
  refine ⟨Oc,Hc,sS',W',G,sG,hOc,hcl,hHcO,hHcS,hO',hdis',hW'O,hW'S,hS'C,?_,
    ?_,hQeq.symm ▸ hAc.diff hOc,hQeq.symm ▸ hnewPL,hQeq.symm ▸ hnewNo,hGdis,hGsub,hGfront⟩
  · intro k hk z
    simp [W',S',O',hk,Homeomorph.setCongr,Equiv.setCongr,Equiv.subtypeEquivProp,
      Equiv.subtypeEquiv,Prod.map]
  · intro k l hkl
    exact (hdis' hkl).mono (hS'C k) (hS'C l)

end PoincareConjecture.M76
