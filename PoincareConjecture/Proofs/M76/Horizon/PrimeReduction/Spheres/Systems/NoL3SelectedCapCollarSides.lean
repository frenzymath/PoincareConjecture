import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.OriginalSphereBicollar
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.Mathlib.ClosedRegionBicollarSides
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSphereConnected
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonWallComplementBall









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

private theorem opposite_sides_of_marked_frontier_neighborhood
    {X : Type*} [TopologicalSpace X] {D S P N U : Set X}
    (hD : IsClosed D) (hregular : closure (interior D) = D)
    (hne : S.Nonempty) (hSF : S ⊆ frontier D) (hU : IsOpen U) (hSU : S ⊆ U)
    (hcover : U ⊆ S ∪ P ∪ N)
    (hP : IsPreconnected P) (hN : IsPreconnected N)
    (hPF : Disjoint P (frontier D)) (hNF : Disjoint N (frontier D)) :
    (P ⊆ interior D ∧ Disjoint N D) ∨ (N ⊆ interior D ∧ Disjoint P D) := by
  obtain ⟨x,hx⟩ := hne
  have hxF := hSF hx
  have hxcl : x ∈ closure (interior D) := hregular.symm ▸ hD.frontier_subset hxF
  obtain ⟨y,hyU,hyint⟩ := mem_closure_iff.mp hxcl U hU (hSU hx)
  have hxcompl : x ∈ closure Dᶜ := by
    rw [frontier_eq_closure_inter_closure] at hxF
    exact hxF.2
  obtain ⟨z,hzU,hzout⟩ := mem_closure_iff.mp hxcompl U hU (hSU hx)
  have hy : y ∈ P ∪ N := by
    rcases hcover hyU with (hf | hp) | hn
    · exact ((hSF hf).2 hyint).elim
    · exact Or.inl hp
    · exact Or.inr hn
  have hz : z ∈ P ∪ N := by
    rcases hcover hzU with (hf | hp) | hn
    · exact (hzout (hD.frontier_subset (hSF hf))).elim
    · exact Or.inl hp
    · exact Or.inr hn
  rcases Poincare.Topology.subset_interior_or_disjoint_of_disjoint_frontier hP hD hPF with hPi | hPo
  · rcases Poincare.Topology.subset_interior_or_disjoint_of_disjoint_frontier hN hD hNF with hNi | hNo
    · exact (hzout (interior_subset (hz.elim (fun h => hPi h) (fun h => hNi h)))).elim
    · exact Or.inl ⟨hPi,hNo⟩
  · rcases Poincare.Topology.subset_interior_or_disjoint_of_disjoint_frontier hN hD hNF with hNi | hNo
    · exact Or.inr ⟨hNi,hPo⟩
    · exact (hy.elim (fun h => disjoint_left.mp hPo h (interior_subset hyint))
        (fun h => disjoint_left.mp hNo h (interior_subset hyint))).elim

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1

theorem ChartwisePLSphere.exists_selected_cap_exterior_half_collar
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R D S T V : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) (hD : PLDomain e D)
    (hfront : frontier D = S ∪ T) (hT : IsClosed T) (hST : Disjoint S T)
    (hV : IsOpen V) (hSV : S ⊆ V) :
    ∃ (t : Finset R) (F : X → (t → ℝ × V3))
      (N : SimplicialComplex ℝ (t → ℝ × V3))
      (HB : N.space ≃ₜ S) (c : (t → ℝ × V3) × ℝ → X) (ε : ℝ) (positive : Bool),
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      InjOn F R ∧ N.space = F '' S ∧ N.faces.Finite ∧
      PolyhedralPLInCharts e c (N.space ×ˢ I) ∧
      Topology.IsEmbedding (fun z : (N.space ×ˢ I : Set ((t → ℝ × V3) × ℝ)) => c z) ∧
      (∀ x : N.space, c ((x : t → ℝ × V3),0) = HB x) ∧
      (∀ z : (N.space ×ˢ I : Set ((t → ℝ × V3) × ℝ)), c z ∈ S ↔ z.1.2 = 0) ∧
      0 < ε ∧ ε ≤ 1 / 2 ∧
      MapsTo c (N.space ×ˢ Icc (-ε) ε) (V ∩ Tᶜ ∩ interior R) ∧
      (∀ η : ℝ, 0 < η → η ≤ ε → IsOpen (c '' (N.space ×ˢ Ioo (-η) η))) ∧
      Disjoint (c '' (N.space ×ˢ (if positive then Ioc 0 ε else Ico (-ε) 0))) D ∧
      (c '' (N.space ×ˢ (if positive then Ico (-ε) 0 else Ioc 0 ε))) ⊆ interior D ∧
      (c '' (N.space ×ˢ (if positive then Icc 0 ε else Icc (-ε) 0))) ∩ D = S := by
  have hSV' : S ⊆ V ∩ Tᶜ := fun x hx =>
    ⟨hSV hx,fun hxT => disjoint_left.mp hST hx hxT⟩
  obtain ⟨t,F,N,HB,c,hFc,hF,hFi,hNF,hN,hc,hci,_,hc0,hcz,ε,hε,hεsmall,hsmall,hopen⟩ :=
    s.exists_original_small_bicollar_with_model hR he hSR (hV.inter hT.isOpen_compl) hSV'
  let A := N.space
  let E := t → ℝ × V3
  let P := c '' (A ×ˢ Ioc 0 ε)
  let M := c '' (A ×ˢ Ico (-ε) 0)
  let O := c '' (A ×ˢ Ioo (-ε) ε)
  have hsub : A ×ˢ Icc (-ε) ε ⊆ A ×ˢ I :=
    prod_mono subset_rfl (Icc_subset_Icc (by linarith) (by linarith))
  have hPsub : A ×ˢ Ioc 0 ε ⊆ A ×ˢ Icc (-ε) ε :=
    prod_mono subset_rfl (fun x hx => ⟨by linarith [hx.1],hx.2⟩)
  have hMsub : A ×ˢ Ico (-ε) 0 ⊆ A ×ˢ Icc (-ε) ε :=
    prod_mono subset_rfl (fun x hx => ⟨hx.1,by linarith [hx.2]⟩)
  have hAc : IsConnected A := isConnected_iff_connectedSpace.mpr
    (HB.connectedSpace_iff.mpr (isConnected_iff_connectedSpace.mp s.isConnected))
  have hSO : S ⊆ O := by
    intro x hx
    refine ⟨((HB.symm ⟨x,hx⟩ : E),0),⟨(HB.symm ⟨x,hx⟩).property,by linarith, hε⟩,?_⟩
    exact (hc0 _).trans (congrArg Subtype.val (HB.apply_symm_apply ⟨x,hx⟩))
  have hcover : O ⊆ S ∪ P ∪ M := by
    rintro x ⟨z,hz,rfl⟩
    rcases lt_trichotomy z.2 0 with hn | heq | hp
    · exact Or.inr ⟨z,⟨hz.1,hz.2.1.le,hn⟩,rfl⟩
    · exact Or.inl (Or.inl ((hcz ⟨z,hsub ⟨hz.1,hz.2.1.le,hz.2.2.le⟩⟩).mpr heq))
    · exact Or.inl (Or.inr ⟨z,⟨hz.1,hp,hz.2.2.le⟩,rfl⟩)
  have hPF : Disjoint P (frontier D) := by
    apply disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ hxF
    rcases hfront.subset hxF with hxS | hxT
    · exact hz.2.1.ne' ((hcz ⟨z,hsub (hPsub hz)⟩).mp hxS)
    · exact (hsmall (hPsub hz)).1.2 hxT
  have hMF : Disjoint M (frontier D) := by
    apply disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ hxF
    rcases hfront.subset hxF with hxS | hxT
    · exact hz.2.2.ne ((hcz ⟨z,hsub (hMsub hz)⟩).mp hxS)
    · exact (hsmall (hMsub hz)).1.2 hxT
  have hsides := opposite_sides_of_marked_frontier_neighborhood hD.closed hD.closure_interior
    s.isConnected.nonempty (fun x hx => hfront.symm.subset (Or.inl hx)) (hopen ε hε le_rfl)
    hSO hcover ((hAc.isPreconnected.prod isPreconnected_Ioc).image c
      (hc.continuousOn.mono (hPsub.trans hsub)))
    ((hAc.isPreconnected.prod isPreconnected_Ico).image c
      (hc.continuousOn.mono (hMsub.trans hsub))) hPF hMF
  obtain ⟨positive,hout,hin⟩ : ∃ positive : Bool,
      Disjoint (c '' (A ×ˢ (if positive then Ioc 0 ε else Ico (-ε) 0))) D ∧
      (c '' (A ×ˢ (if positive then Ico (-ε) 0 else Ioc 0 ε))) ⊆ interior D := by
    rcases hsides with ⟨hp,hm⟩ | ⟨hm,hp⟩
    · exact ⟨false,hm,hp⟩
    · exact ⟨true,hp,hm⟩
  refine ⟨t,F,N,HB,c,ε,positive,hFc,hF,hFi,hNF,hN,hc,hci,hc0,hcz,hε,hεsmall,
    hsmall,hopen,hout,hin,?_⟩
  apply Subset.antisymm
  · rintro x ⟨⟨z,hz,rfl⟩,hzD⟩
    by_cases hz0 : z.2 = 0
    · have hzfull : z ∈ A ×ˢ I := hsub ⟨hz.1,by
        cases positive <;> simp only [Bool.false_eq_true,reduceIte] at hz <;>
          constructor <;> linarith [hz.2.1,hz.2.2]⟩
      exact (hcz ⟨z,hzfull⟩).mpr hz0
    · apply False.elim
      apply disjoint_left.mp hout _ hzD
      refine ⟨z,⟨hz.1,?_⟩,rfl⟩
      cases positive <;> simp only [Bool.false_eq_true,reduceIte] at hz ⊢
      · exact ⟨hz.2.1,lt_of_le_of_ne hz.2.2 hz0⟩
      · exact ⟨lt_of_le_of_ne hz.2.1 (Ne.symm hz0),hz.2.2⟩
  · intro x hx
    refine ⟨?_,hD.closed.frontier_subset (hfront.symm.subset (Or.inl hx))⟩
    refine ⟨((HB.symm ⟨x,hx⟩ : E),0),⟨(HB.symm ⟨x,hx⟩).property,?_⟩,
      (hc0 _).trans (congrArg Subtype.val (HB.apply_symm_apply ⟨x,hx⟩))⟩
    cases positive <;> simp only [Bool.false_eq_true,reduceIte] <;> constructor <;> linarith

end PoincareConjecture.M76
