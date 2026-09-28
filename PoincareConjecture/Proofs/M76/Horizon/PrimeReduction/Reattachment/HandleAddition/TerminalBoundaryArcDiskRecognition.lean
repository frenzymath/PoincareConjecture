import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcSignedRegion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.BoundaryLoopCharts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.BoundaryLoopIntrinsicCharts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.BoundaryDisks.CompactSurfaceDiskRecognition



set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_original_disk_of_flat_boundary_region
    {X ι : Type*} [MetricSpace X] [Nonempty X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} (he : PLDomain e R)
    [PreconnectedSpace (frontier R)]
    {O : Set (frontier R)} (hO : IsOpen O) (hK : IsCompact (closure O))
    (hsc : IsSimplyConnected O) (hproper : closure O ≠ univ)
    (hconn : IsConnected (frontier O))
    (hcharts : ∀ x ∈ (Subtype.val : frontier R → X) '' frontier O,
      ∃ (T : OpenPartialHomeomorph X V3) (ell psi : V3 →ᴬ[ℝ] ℝ) (u v : V3),
        x ∈ T.source ∧ T x = 0 ∧
        (∀ i,(e i).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
        ell.contLinear u = 0 ∧ psi.contLinear u = 1 ∧
        ell.contLinear v = 1 ∧ psi.contLinear v = 0 ∧
        (∀ y ∈ T.source,y ∈ frontier R ↔ ell (T y) = 0) ∧
        ∀ y ∈ T.source,y ∈ Subtype.val '' frontier O ↔
          ell (T y) = 0 ∧ psi (T y) = 0) :
    ∃ (H : closedBall (0 : V2) 1 ≃ₜ ((Subtype.val : frontier R → X) '' closure O))
      (j : V2 → X), PolyhedralPLInCharts e j (closedBall 0 1) ∧
      Topology.IsEmbedding (fun z : closedBall (0 : V2) 1 => j z) ∧
      (∀ z : closedBall (0 : V2) 1,j z = (H z : X)) ∧
      j '' closedBall 0 1 = Subtype.val '' closure O ∧
      ∀ z : closedBall (0 : V2) 1,j z ∈ Subtype.val '' frontier O ↔
        (z : V2) ∈ sphere 0 1 := by
  classical
  let K : Set X := Subtype.val '' closure O
  let M : Set X := Subtype.val '' frontier O
  have hM (y : frontier R) : (y : X) ∈ M ↔ y ∈ frontier O :=
    Subtype.val_injective.mem_set_image
  have hKI (y : frontier R) : (y : X) ∈ K ↔ y ∈ closure O :=
    Subtype.val_injective.mem_set_image
  have hcompact : IsCompact (frontier O) := hK.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hflats : ∀ x ∈ frontier O,∃ q : OpenPartialHomeomorph (frontier R) (ℝ × ℝ),
      x ∈ q.source ∧ ∃ (m : (ℝ × ℝ) →L[ℝ] ℝ) (w : ℝ × ℝ),m w = 1 ∧
        Convex ℝ q.target ∧ ∀ y ∈ q.source,y ∈ frontier O ↔ m (q y) = 0 := by
    intro x hx
    obtain ⟨T,ell,psi,u,v,hxT,hTx,hTc,hu,hpu,hv,hpv,hF,hL⟩ :=
      hcharts x (mem_image_of_mem Subtype.val hx)
    obtain ⟨q,a,r,m,w,ε,hε,hxq,hqs,hqx,hqt,hcv,hra,hm,hqf,hqi,hql,hqvalue⟩ :=
      exists_convex_intrinsic_loop_chart_with_value T ell psi u v hu hpu hv hF hL
        x hxT hTx (mem_image_of_mem Subtype.val hx)
    exact ⟨q,hxq,m,w,hm,hcv,fun y hy => (hM y).symm.trans (hql y hy)⟩
  obtain ⟨hfront,hclosedsc⟩ := isSimplyConnected_closure_of_convex_flat_frontier
    hO hsc hproper hcompact hconn hflats
  let : SimplyConnectedSpace K := Topology.IsEmbedding.subtypeVal.isSimplyConnected_image.mpr hclosedsc
  have hrestrict (T : OpenPartialHomeomorph X V3)
      (hc : ∀ i,(e i).symm.trans T ∈ piecewiseAffineGroupoid V3)
      (V : Set X) (hV : IsOpen V) :
      ∀ i,(e i).symm.trans (T.restrOpen V hV) ∈ piecewiseAffineGroupoid V3 := by
    intro i
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact ((mem_piecewiseAffineGroupoid_iff_forward _).mp (hc i)).mono
      ((e i).symm.trans (T.restrOpen V hV)).open_source (fun y hy => ⟨hy.1,hy.2.1⟩)
  apply exists_compact_original_simplyConnected_marked_disk e he (hK.image continuous_subtype_val) ?_ ?_
  · rintro x ⟨z,hz,rfl⟩
    by_cases hzr : z ∈ frontier O
    · obtain ⟨T,ell,psi,u,v,hzT,hTz,hTc,hu,hpu,hv,hpv,hF,hL⟩ :=
        hcharts z (mem_image_of_mem Subtype.val hzr)
      obtain ⟨q,a,r,m,w,ε,hε,hzq,hqs,hqz,hqt,hcv,hra,hm,hqf,hqi,hql,hqvalue⟩ :=
        exists_convex_intrinsic_loop_chart_with_value T ell psi u v hu hpu hv hF hL
          z hzT hTz (mem_image_of_mem Subtype.val hzr)
      obtain ⟨V,hV,hVs⟩ := isOpen_induced_iff.mp q.open_source
      have hzV : (z : X) ∈ V := hVs.symm.subset hzq
      have hreg : closure (interior (closure O)) = closure O := by
        apply Subset.antisymm
        · exact closure_minimal interior_subset isClosed_closure
        · exact closure_mono hO.subset_interior_closure
      have hsign := halfspace_of_convex_linear_frontier_chart isClosed_closure hreg
        (hfront.symm ▸ hzr) q hzq m hcv (by
          intro y hy
          rw [hfront]
          exact (hM y).symm.trans (hql y hy))
      have hqsV (y : frontier R) (hy : (y : X) ∈ V) : y ∈ q.source := hVs.symm ▸ hy
      have hside : (∀ y ∈ (T.restrOpen V hV).source,y ∈ K ↔
          ell (T y) = 0 ∧ 0 ≤ psi (T y)) ∨
          (∀ y ∈ (T.restrOpen V hV).source,y ∈ K ↔
          ell (T y) = 0 ∧ psi (T y) ≤ 0) := by
        rcases hsign with hp | hn
        · left
          intro y hy
          constructor
          · rintro ⟨yy,hyy,rfl⟩
            exact ⟨(hF yy hy.1).mp yy.property,by
              rw [←hqvalue yy (hqsV yy hy.2)]
              exact (hp yy (hqsV yy hy.2)).mp hyy⟩
          · rintro ⟨hyF,hyp⟩
            let yy : frontier R := ⟨y,(hF y hy.1).mpr hyF⟩
            exact (hKI yy).mpr ((hp yy (hqsV yy hy.2)).mpr (by
              rw [hqvalue yy (hqsV yy hy.2)]; exact hyp))
        · right
          intro y hy
          constructor
          · rintro ⟨yy,hyy,rfl⟩
            exact ⟨(hF yy hy.1).mp yy.property,by
              rw [←hqvalue yy (hqsV yy hy.2)]
              exact (hn yy (hqsV yy hy.2)).mp hyy⟩
          · rintro ⟨hyF,hyp⟩
            let yy : frontier R := ⟨y,(hF y hy.1).mpr hyF⟩
            exact (hKI yy).mpr ((hn yy (hqsV yy hy.2)).mpr (by
              rw [hqvalue yy (hqsV yy hy.2)]; exact hyp))
      refine ⟨T.restrOpen V hV,⟨hzT,hzV⟩,hrestrict T hTc V hV,Or.inr ?_⟩
      rcases hside with hp | hn
      · exact ⟨ell,psi,u,v,hpu,hv,hpv,hp,fun y hy => hL y hy.1⟩
      · refine ⟨ell,-psi,-u,v,?_,hv,?_,?_,?_⟩
        · simpa using hpu
        · simpa using hpv
        · intro y hy
          change y ∈ K ↔ ell (T y) = 0 ∧ 0 ≤ -psi (T y)
          simpa only [neg_nonneg] using hn y hy
        · intro y hy; simpa using hL y hy.1
    · have hzO : z ∈ O := by
        have hh : z ∈ closure O \ frontier O := ⟨hz,hzr⟩
        rwa [closure_sdiff_frontier,hO.interior_eq] at hh
      obtain ⟨V,hV,hVO⟩ := isOpen_induced_iff.mp hO
      have hzV : (z : X) ∈ V := hVO.symm.subset hzO
      obtain ⟨ell,v,T,hv,hzT,hzero,hTc,hhalf⟩ := he.halfspace z z.property
      have hell : ell.toAffineMap.linear ≠ 0 := by
        intro hh
        have hv' : ell.toAffineMap.linear v = 1 := hv
        rw [hh] at hv'
        exact zero_ne_one hv'
      have hTF := T.isImage_frontier_of_affine_nonneg ell hell hhalf
      refine ⟨T.restrOpen V hV,⟨hzT,hzV⟩,hrestrict T hTc V hV,Or.inl
        ⟨ell,v,hv,?_,?_⟩⟩
      · intro y hy
        constructor
        · rintro ⟨yy,hyy,rfl⟩
          exact (hTF.apply_mem_iff hy.1).mpr yy.property
        · intro hy0
          let yy : frontier R := ⟨y,(hTF.apply_mem_iff hy.1).mp hy0⟩
          exact (hKI yy).mpr (subset_closure (hVO.symm ▸ hy.2))
      · apply disjoint_left.mpr
        rintro y hy ⟨yy,hyy,rfl⟩
        exact hyy.2 (hO.interior_eq.symm ▸ (hVO.symm ▸ hy.2))
  · obtain ⟨x,hx⟩ := hconn.nonempty
    exact ⟨x,⟨x,frontier_subset_closure hx,rfl⟩,mem_image_of_mem Subtype.val hx⟩

theorem PLDomain.exists_original_disk_of_two_arc_boundary_region
    {X ι E F : Type*} [MetricSpace X] [Nonempty X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} (he : PLDomain e R)
    [PreconnectedSpace (frontier R)]
    {U : Set E} {V : Set F} {a b : E} {c d : F}
    (hU : IsFinitePLBallPair ℝ U {a,b}) (hV : IsFinitePLBallPair ℝ V {c,d})
    (hab : a ≠ b) (hcd : c ≠ d) {f : E → X} {g : F → X}
    (hf : PolyhedralPLInCharts e f U) (hg : PolyhedralPLInCharts e g V)
    (hfi : InjOn f U) (hgi : InjOn g V)
    (h0 : f a = g c) (h1 : f b = g d)
    (hinter : f '' U ∩ g '' V = {f a,f b})
    {O : Set (frontier R)} (hO : IsOpen O) (hK : IsCompact (closure O))
    (hsc : IsSimplyConnected O) (hproper : closure O ≠ univ)
    (hrim : (Subtype.val : frontier R → X) '' frontier O = f '' U ∪ g '' V) :
    ∃ (H : closedBall (0 : V2) 1 ≃ₜ ((Subtype.val : frontier R → X) '' closure O))
      (j : V2 → X), PolyhedralPLInCharts e j (closedBall 0 1) ∧
      Topology.IsEmbedding (fun z : closedBall (0 : V2) 1 => j z) ∧
      (∀ z : closedBall (0 : V2) 1,j z = (H z : X)) ∧
      j '' closedBall 0 1 = Subtype.val '' closure O ∧
      ∀ z : closedBall (0 : V2) 1,j z ∈ f '' U ∪ g '' V ↔
        (z : V2) ∈ sphere 0 1 := by
  have haU : a ∈ U := hU.1 (by simp)
  have hcV : c ∈ V := hV.1 (by simp)
  have hconn : IsConnected (f '' U ∪ g '' V) :=
    (hU.isConnected.image f hf.continuousOn).union
      ⟨f a,mem_image_of_mem f haU,⟨c,hcV,h0.symm⟩⟩
      (hV.isConnected.image g hg.continuousOn)
  have hconnO : IsConnected (frontier O) := by
    have hconn' : IsConnected ((Subtype.val : frontier R → X) '' frontier O) := hrim.symm ▸ hconn
    exact ⟨Set.image_nonempty.mp hconn'.nonempty,
      Topology.IsInducing.subtypeVal.isPreconnected_image.mp hconn'.isPreconnected⟩
  have hfront : f '' U ∪ g '' V ⊆ frontier R := by
    rw [←hrim]
    rintro _ ⟨x,_,rfl⟩
    exact x.property
  obtain ⟨H,j,hj,hji,hjH,himage,hjrim⟩ :=
    he.exists_original_disk_of_flat_boundary_region hO hK hsc hproper hconnO (by
      intro x hx
      obtain ⟨T,ell,psi,u,v,hxT,_,hTx,hTc,hu,hpu,hv,hpv,hF,hL⟩ :=
        he.exists_boundary_two_interval_loop_chart hU hV hab hcd hf hg hfi hgi
          h0 h1 hinter hfront (hrim.subset hx) isOpen_univ (mem_univ x)
      exact ⟨T,ell,psi,u,v,hxT,hTx,hTc,hu,hpu,hv,hpv,hF,fun y hy =>
        by rw [hrim]; exact hL y hy⟩)
  exact ⟨H,j,hj,hji,hjH,himage,by simpa only [hrim] using hjrim⟩

end PoincareConjecture.M76
