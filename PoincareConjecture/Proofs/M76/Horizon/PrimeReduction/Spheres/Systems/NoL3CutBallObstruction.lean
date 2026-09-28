import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3ConfinedBallComponents
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.AnnulusSides

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem exists_collar_end_in_interior
    {X V : Type*} [TopologicalSpace X] [TopologicalSpace V]
    {A : Set V} {D : Set X} {c : V × ℝ → X} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hc : ContinuousOn c (A ×ˢ Icc (-1 : ℝ) 1))
    (hci : InjOn c (A ×ˢ Icc (-1 : ℝ) 1))
    (hopen : IsOpen (c '' (A ×ˢ Ioo (-ε) ε)))
    (hcenter : c '' (A ×ˢ ({0} : Set ℝ)) = frontier D)
    (hne : (frontier D).Nonempty) (hregular : closure (interior D) = D) :
    ∃ b : Bool, (c '' (A ×ˢ ({if b then ε else -ε} : Set ℝ)) ∩ interior D).Nonempty := by
  obtain ⟨y, hy⟩ := hne
  have hyD : y ∈ closure (interior D) := by
    rw [hregular]
    have hclosed : IsClosed D := hregular ▸ isClosed_closure
    exact hclosed.frontier_subset hy
  have hyO : y ∈ c '' (A ×ˢ Ioo (-ε) ε) := by
    rw [←hcenter] at hy
    obtain ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩ := hy
    have ht0 : t = 0 := ht
    subst t
    exact ⟨(z,0),⟨hz,by constructor <;> linarith⟩,rfl⟩
  obtain ⟨w, hwO, hwD⟩ := mem_closure_iff.mp hyD _ hopen hyO
  obtain ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩ := hwO
  have ht0 : t ≠ 0 := by
    intro ht0
    have hfront : c (z,t) ∈ frontier D := by
      rw [←hcenter]
      exact ⟨(z,t),⟨hz,ht0⟩,rfl⟩
    exact hfront.2 hwD
  have hcont : ContinuousOn (fun u : ℝ => c (z,u)) (Icc (-1 : ℝ) 1) :=
    hc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu => ⟨hz,hu⟩)
  have havoid (I : Set ℝ) (hI : I ⊆ Icc (-1 : ℝ) 1) (hI0 : 0 ∉ I) :
      Disjoint ((fun u : ℝ => c (z,u)) '' I) (frontier D) := by
    apply disjoint_left.mpr
    intro w hw hfront
    obtain ⟨u,hu,huEq⟩ := hw
    rw [←huEq,←hcenter] at hfront
    obtain ⟨⟨z',v⟩,⟨hz',hv⟩,heq⟩ := hfront
    have hv0 : v = 0 := hv
    have hpair : (z',v) = (z,u) := hci
      (show (z',v) ∈ A ×ˢ Icc (-1 : ℝ) 1 from ⟨hz',by subst v; norm_num⟩)
      (show (z,u) ∈ A ×ˢ Icc (-1 : ℝ) 1 from ⟨hz,hI hu⟩) heq
    have hu0 : u = 0 := (congrArg Prod.snd hpair).symm.trans hv0
    exact hI0 (hu0 ▸ hu)
  rcases lt_or_gt_of_ne ht0 with htneg | htpos
  · have hI : Ico (-ε) 0 ⊆ Icc (-1 : ℝ) 1 := by
      intro u hu
      constructor <;> linarith [hu.1,hu.2]
    have hside : (fun u : ℝ => c (z,u)) '' Ico (-ε) 0 ⊆ interior D :=
      ((isConnected_Ico (by linarith : -ε < 0)).image _ (hcont.mono hI)).isPreconnected.subset_interior_of_avoids_frontier
        (havoid _ hI (by simp))
          ⟨c (z,t),⟨t,⟨ht.1.le,htneg⟩,rfl⟩,hwD⟩
    refine ⟨false,c (z,-ε),⟨(z,-ε),⟨hz,by simp⟩,rfl⟩,?_⟩
    exact hside ⟨-ε,⟨le_rfl,by linarith⟩,rfl⟩
  · have hI : Ioc 0 ε ⊆ Icc (-1 : ℝ) 1 := by
      intro u hu
      constructor <;> linarith [hu.1,hu.2]
    have hside : (fun u : ℝ => c (z,u)) '' Ioc 0 ε ⊆ interior D :=
      ((isConnected_Ioc hε).image _ (hcont.mono hI)).isPreconnected.subset_interior_of_avoids_frontier
        (havoid _ hI (by simp))
          ⟨c (z,t),⟨t,⟨htpos,ht.2.le⟩,rfl⟩,hwD⟩
    refine ⟨true,c (z,ε),⟨(z,ε),⟨hz,by simp⟩,rfl⟩,?_⟩
    exact hside ⟨ε,⟨hε,le_rfl⟩,rfl⟩

theorem HasNoPuncturedSphereComponents.not_ball_with_retained_collar
    {X V E ι κ : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Finite κ]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {Q D S : Set X} {f : X → E} {A : Set V} {c : V × ℝ → X} {ε : ℝ}
    (hno : HasNoPuncturedSphereComponents e f Q)
    (ball : ChartwisePLBall e D S)
    (hQ : IsCompact Q) (hPL : PLDomain e Q)
    (B : κ → Set X) (sB : ∀ i, ChartwisePLSphere e (B i))
    (hBdis : Pairwise fun i j => Disjoint (B i) (B j))
    (hfront : frontier Q = ⋃ i, B i)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f D) (hSQ : Disjoint S Q)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hc : ContinuousOn c (A ×ˢ Icc (-1 : ℝ) 1))
    (hci : InjOn c (A ×ˢ Icc (-1 : ℝ) 1))
    (hopen : IsOpen (c '' (A ×ˢ Ioo (-ε) ε)))
    (hcenter : c '' (A ×ˢ ({0} : Set ℝ)) = S)
    (hne : S.Nonempty)
    (hend : ∀ b : Bool, c '' (A ×ˢ ({if b then ε else -ε} : Set ℝ)) ⊆ Q) : False := by
  obtain ⟨b,x,hxb,hxD⟩ := exists_collar_end_in_interior hε hε1 hc hci hopen
    (hcenter.trans ball.frontier_eq.symm) (ball.frontier_eq.symm ▸ hne) ball.closure_interior
  have hxQ := hend b hxb
  have hcc : connectedComponentIn Q x ⊆ interior D :=
    isPreconnected_connectedComponentIn.subset_interior_of_avoids_frontier
      (by rw [ball.frontier_eq]; exact hSQ.symm.mono (connectedComponentIn_subset _ _) Subset.rfl)
      ⟨x,mem_connectedComponentIn hxQ,hxD⟩
  exact hno.not_component_subset_ball ball hQ hPL B sB hBdis hfront hf hfi hxQ
    (hcc.trans interior_subset)

end PoincareConjecture.M76
