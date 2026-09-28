import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.MaximalOriginalSphereCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.OriginalCappedPLDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedSphereCutComparison
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.NewPortComponentAlternatives

set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Geometry Geometry.SeparatedSphereCaps
namespace PoincareConjecture.M76
universe u
local notation "V3" => (Fin 3 → ℝ)

theorem exists_maximal_capped_sphere_cut_from_cut
    {X κ : Type u} {ι E : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype κ] [DecidableEq κ]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (c : MarkedSphereCut e R κ)
    {f : X → E} (K₀ : SimplicialComplex ℝ E) (g : E → X)
    (hgPL : PolyhedralPLInCharts e g K₀.space) (hgi : InjOn g K₀.space)
    (hreal : ∀ x ∈ R,f x ∈ K₀.space ∧ g (f x) = x)
    (hno : HasNoPuncturedSphereComponents e f c.carrier)
    (hmax : ∀ (ν : Type u) [Fintype ν] (d : MarkedSphereCut e R ν),
      HasNoPuncturedSphereComponents e f d.carrier → Fintype.card ν ≤ Fintype.card κ)
    (hU : IsOpen U) (hSU : ∀ i,c.spheres i ⊆ U) :
    ∃ cut : MarkedSphereCut e R κ,cut.spheres = c.spheres ∧
      c.carrier ⊆ cut.carrier ∧ closure (⋃ i,cut.collar i) ⊆ U ∧
      HasNoPuncturedSphereComponents e f cut.carrier ∧
      ∃ P : Set X,IsCompact P ∧ R ⊆ interior P ∧ PLDomain e P ∧
∃ (τ : Type u) (_ : Fintype τ) (F : X → (τ → ℝ × V3))
  (W : Set ((τ → ℝ × V3) × ((κ × Bool) → ℝ))),
  let A : κ × Bool → Set ((τ → ℝ × V3) × ((κ × Bool) → ℝ)) :=
    fun j => cap j (F '' cut.ports j)
  let D := lift '' (F '' cut.carrier) ∪ ⋃ j, A j
      let Qouter := P \ ⋃ i,cut.collar i
      PLDomain e Qouter ∧ frontier Qouter = frontier P ∪ ⋃ j,cut.ports j ∧
      IsCompact Qouter ∧
      InjOn F Qouter ∧
      W = (lift '' (F '' Qouter) ∪ ⋃ j,A j) \ lift '' (F '' frontier P) ∧
      (∀ j,A j ∩ lift '' (F '' Qouter) = lift '' (F '' cut.ports j)) ∧
      (∀ x ∈ Qouter,∃ (j : ι) (V : Set X) (a : (τ → ℝ × V3) →ᴬ[ℝ] V3),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (e j).source ∧ EqOn (a ∘ F) (e j) V) ∧
      (∃ K : SimplicialComplex ℝ (τ → ℝ × V3),K.faces.Finite ∧ K.space = F '' Qouter) ∧
      Disjoint (lift '' (F '' frontier P)) (⋃ j,A j) ∧
  D ⊆ W ∧
  Continuous F ∧
  (∀ j, LocallyPiecewiseAffineOn (F ∘ (e j).symm) (e j).target) ∧
  InjOn F cut.carrier ∧
  (∀ j, IsFinitePLBallPair V3 (A j) (lift '' (F '' cut.ports j))) ∧
  (∀ j, A j ∩ lift '' (F '' cut.carrier) = lift '' (F '' cut.ports j)) ∧
  Pairwise (fun i j => Disjoint (A i) (A j)) ∧
  ∃ atlas : W → OpenPartialHomeomorph W V3,
    (∀ p : W, p ∈ (atlas p).source) ∧ PLDomain atlas Set.univ ∧
    (∀ p : W, ∃ (B : Set ((τ → ℝ × V3) × ((κ × Bool) → ℝ)))
      (a : ((τ → ℝ × V3) × ((κ × Bool) → ℝ)) → V3)
      (a' : V3 → ((τ → ℝ × V3) × ((κ × Bool) → ℝ))),
      FinitePiecewiseAffineOn a B ∧
      FinitePiecewiseAffineOn a' (Metric.closedBall (0 : V3) 1) ∧
      (∀ x ∈ (atlas p).source, (x : (τ → ℝ × V3) × ((κ × Bool) → ℝ)) ∈ B ∧
        atlas p x = a x) ∧
      (atlas p).target ⊆ interior (Metric.closedBall (0 : V3) 1) ∧
      ∀ y ∈ (atlas p).target,
        ((atlas p).symm y : (τ → ℝ × V3) × ((κ × Bool) → ℝ)) = a' y) ∧
    let v : W → ((τ → ℝ × V3) × ((κ × Bool) → ℝ)) := Subtype.val
    PLDomain atlas (v ⁻¹' D) ∧ IsCompact (v ⁻¹' D) ∧
    frontier (v ⁻¹' D) = v ⁻¹' (lift '' (F '' frontier R)) ∧
    (∀ j, Nonempty (ChartwisePLBall atlas
      (v ⁻¹' A j) (v ⁻¹' lift '' (F '' cut.ports j)))) ∧
    (∀ j, v ⁻¹' A j ⊆ interior (v ⁻¹' D)) ∧
    ∀ (S : Set W), ChartwisePLSphere atlas S → S ⊆ interior (v ⁻¹' D) →
      (¬ ∃ A' : Set W, A' ⊆ v ⁻¹' D ∧ Nonempty (ChartwisePLBall atlas A' S)) →
      ∃ (G : W ≃ₜ W) (V : Set W),
        IsCompact V ∧ V ⊆ interior (v ⁻¹' D) ∧ EqOn G id Vᶜ ∧
        (∀ i j, (atlas i).symm.trans (G.toOpenPartialHomeomorph.trans (atlas j)) ∈
          piecewiseAffineGroupoid V3) ∧
        (∀ i j, (atlas i).symm.trans (G.symm.toOpenPartialHomeomorph.trans (atlas j)) ∈
          piecewiseAffineGroupoid V3) ∧
        Nonempty (ChartwisePLSphere atlas (G '' S)) ∧
        Disjoint (G '' S) (v ⁻¹' ⋃ j, A j) ∧
      ∃ (T : Set X) (_sT : ChartwisePLSphere e T),
        T ⊆ interior cut.carrier ∧
        lift '' (F '' T) = v '' (G '' S) ∧
        (¬ ∃ A' : Set X, A' ⊆ cut.carrier ∧ Nonempty (ChartwisePLBall e A' T)) ∧
        ∃ (d : MarkedSphereCut e R (Option κ)) (x : X),
          d.spheres = (fun i : Option κ => i.elim T cut.spheres) ∧
          (∀ i, d.collar (some i) = cut.collar i) ∧
          (∀ i j, d.ports (some i,j) = cut.ports (i,j)) ∧
          d.carrier = cut.carrier \ d.collar none ∧
          closure (d.collar none) ⊆ interior cut.carrier ∧
          Nonempty (OriginalFiniteSphereCollar e cut.carrier T (d.collar none)
            (fun j => d.ports (none,j))) ∧
          x ∈ d.carrier ∧
          HasPuncturedSphereModel e f (connectedComponentIn d.carrier x) ∧
          (∀ j : Bool, ¬ ∃ A' : Set X, A' ⊆ d.carrier ∧
            Nonempty (ChartwisePLBall e A' (d.ports (none,j)))) ∧
          ∃ j : Bool, d.ports (none,j) ⊆ connectedComponentIn d.carrier x ∧
            ((d.ports (none,!j) ⊆ connectedComponentIn d.carrier x ∧
              connectedComponentIn cut.carrier x =
                connectedComponentIn d.carrier x ∪ closure (d.collar none)) ∨
             (Disjoint (d.ports (none,!j)) (connectedComponentIn d.carrier x) ∧
              ∃ y ∈ d.ports (none,!j),
                connectedComponentIn cut.carrier x =
                  (connectedComponentIn d.carrier x ∪ connectedComponentIn d.carrier y) ∪
                    closure (d.collar none) ∧
                Disjoint (connectedComponentIn d.carrier y)
                  (connectedComponentIn d.carrier x))) := by
  classical
  have hSopen (i : κ) : c.spheres i ⊆ c.collar i := by
    intro x hx
    have h := (c.openCoordinates i (⟨x,hx⟩, ⟨(1/2 : ℝ), by norm_num⟩)).mpr
      (by norm_num)
    rwa [c.center i ⟨x,hx⟩] at h
  obtain ⟨P,hP,hRP,heP,tN,N,HB,cN,δ,H,sB,t,F,K,HQ,C,
    hmodel,hOopen,hclosedDisjoint,hmark,hO,hOcl,hQo,heQo,hQof,hQi,heQi,hQif,
    hBdis,hBins,hOldP,hOldR,hQoU,hQiU,hSQ,hFc,hF,hFi,hK,hKs,hHQ,hproj,
    hball,hattach,hcapsdis,hOldPdis,hOldRdis,hOutside,hC,hCs,hDW,
    cut,hcutS,hcutO,hcutB,hcutH,atlas,hcenter,hatlas,hrep,heD,hD,hDf,
    hcapBalls,hcapsInterior,havoid⟩ :=
    exists_original_capped_pl_domain c.spheres c.spherePL c.sphereDisjoint hR he
      c.sphereInterior (hU.inter (isOpen_iUnion c.collarOpen))
      (fun i x hx => ⟨hSU i hx,subset_iUnion c.collar i (hSopen i hx)⟩)
  let O := ⋃ i, cN i '' ((N i).space ×ˢ Ioo (-(δ i / 2)) (δ i / 2))
  have hcarrier : cut.carrier = R \ O := by
    simp only [MarkedSphereCut.carrier, hcutO, O]
  have hmono : c.carrier ⊆ cut.carrier := by
    rw [hcarrier]
    intro x hx
    exact ⟨hx.1, fun h => hx.2 (hOcl (subset_closure h)).1.2⟩
  have hnoCut := c.noPuncturedSphereComponents_mono cut hcutS hmono hR.isClosed
    K₀ g hgPL hgi hreal hno
  have hQiQo : cut.carrier ⊆ P \ O := by
    rw [hcarrier]
    exact fun x hx => ⟨interior_subset (hRP hx.1),hx.2⟩
  have hport (j : κ × Bool) : cut.ports j ⊆ cut.carrier := by
    intro x hx
    apply cut.plCut.closed.frontier_subset
    rw [cut.frontierCut]
    exact Or.inr (mem_iUnion.mpr ⟨j,hx⟩)
  have hattachCut (j : κ × Bool) :
      cap j (F '' cut.ports j) ∩ lift '' (F '' cut.carrier) =
        lift '' (F '' cut.ports j) := by
    apply Subset.antisymm
    · intro x hx
      have hh : x ∈ cap j (F '' cut.ports j) ∩ lift '' K.space :=
        ⟨hx.1, image_mono (image_mono hQiQo |>.trans hKs.symm.subset) hx.2⟩
      simpa only [hcutB] using (hattach j).subset (by simpa only [hcutB] using hh)
    · intro x hx
      exact ⟨by simpa only [hcutB] using (hball j).1 (by simpa only [hcutB] using hx),
        image_mono (image_mono (hport j)) hx⟩
  have hsupport : closure (⋃ i,cut.collar i) ⊆ U := by
    simpa only [hcutO,O] using hOcl.trans (inter_subset_left.trans inter_subset_left)
  have houterInj : InjOn F (P \ ⋃ i,cut.collar i) := by
    simpa only [hcutO,O] using hFi
  have houterAttach (j : κ × Bool) :
      cap j (F '' cut.ports j) ∩ lift '' (F '' (P \ ⋃ i,cut.collar i)) =
        lift '' (F '' cut.ports j) := by
    simpa only [hcutB,hcutO,O,← hKs] using hattach j
  refine ⟨cut,hcutS,hmono,hsupport,hnoCut,P,hP,hRP,heP,t,inferInstance,F,_,
    (by simpa only [hcutO,O] using heQo),
    (by simpa only [hcutO,hcutB,O] using hQof),
    (by simpa only [hcutO,O] using hQo),
    houterInj,?_,houterAttach,?_,?_,?_,?_,hFc,hF,hFi.mono hQiQo,
    ?_,hattachCut,?_,atlas,hcenter,hatlas,hrep,?_,?_,?_,?_,?_,?_⟩
  · rw [hCs,hKs]
    simp only [hcutO,hcutB]
  · simpa only [hcutO,O] using hproj
  · exact ⟨K,hK,by simpa only [hcutO,O] using hKs⟩
  · simpa only [hcutB] using hOldPdis
  · simpa only [hcarrier,hcutB,O] using hDW
  · simpa only [hcutB] using hball
  · simpa only [hcutB] using hcapsdis
  · simpa only [hcarrier,hcutB,O] using heD
  · simpa only [hcarrier,hcutB,O] using hD
  · simpa only [hcarrier,hcutB,O] using hDf
  · simpa only [hcutB] using hcapBalls
  · simpa only [hcarrier,hcutB,O] using hcapsInterior
  · intro S sS hS hnontrivial
    obtain ⟨G,V,hV,hVD,hfix,hGPL,hGinv,hGS,hclear,hreturn⟩ := havoid S sS
    refine ⟨G,V,hV,?_,hfix,hGPL,hGinv,hGS,?_,?_⟩
    · simpa only [hcarrier,hcutB,O] using hVD
    · simpa only [hcutB] using hclear
    obtain ⟨T,⟨sT⟩,hT,himage,hnot⟩ := hreturn (by simpa only [hcarrier,hcutB,O] using hS)
    have hT' : T ⊆ interior cut.carrier := by simpa only [hcarrier,O] using hT
    have hnot' : ¬ ∃ A' : Set X, A' ⊆ cut.carrier ∧ Nonempty (ChartwisePLBall e A' T) := by
      simpa only [hcarrier,O] using hnot (by simpa only [hcarrier,hcutB,O] using hnontrivial)
    obtain ⟨d,x,hdS,hdO,hdB,hdC,hdinside,hx,hpunctured,hraw,htransfer⟩ :=
      cut.exists_punctured_extension_with_original_collar f hmax sT hT'
        isOpen_univ (subset_univ T)
    have hdinside' := hdinside.trans inter_subset_right
    refine ⟨T,sT,hT',himage,hnot',d,x,hdS,hdO,hdB,hdC,hdinside',hraw,hx,hpunctured,?_,?_⟩
    · rintro j ⟨A',hA',⟨bA'⟩⟩
      obtain ⟨A'',hA'',_,_,hsub⟩ := htransfer j A' bA' hA'
      exact hnot' ⟨A'',hsub,hA''⟩
    · obtain ⟨j,hj⟩ :=
        cut.exists_new_port_subset_of_punctured_component d hdC hdinside' hnoCut hx hpunctured
      obtain ⟨y,hy,hformula,hcases⟩ :=
        cut.restored_component_of_new_port d hdC hdinside' hx j hj
      refine ⟨j,hj,?_⟩
      rcases hcases with hsame | ⟨hother,hdis⟩
      · exact Or.inl hsame
      · exact Or.inr ⟨hother,y,hy,hformula,hdis⟩

end PoincareConjecture.M76
