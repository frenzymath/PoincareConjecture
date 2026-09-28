import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalBallDiskAttachment
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalSeparatedProductSpheres
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalWholeDiskProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.CompatibleChartSphereBall
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.OriginalCapNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedArcSphereObstruction
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSphereConnected
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalStripPuncturedModel










set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "J" => Icc (-(1/2 : ℝ)) (1/2)

private theorem ball_contact_or_containment
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {U B T N : Set X}
    (u : ChartwisePLBall e U T) (b : ChartwisePLBall e B N)
    (hcontact : U ∩ N ⊆ frontier U) :
    U ⊆ B ∨ U ∩ B = U ∩ N := by
  have hdis : Disjoint (interior U) (frontier B) := by
    rw [b.frontier_eq]
    exact disjoint_left.mpr (fun x hx hn =>
      (hcontact ⟨interior_subset hx,hn⟩).2 hx)
  rcases preconnected_interior_or_exterior_of_frontier_avoidance
    b.isCompact.isClosed u.isConnected_interior.isPreconnected hdis with hin | hout
  · left
    rw [← u.closure_interior]
    exact closure_minimal (hin.trans interior_subset) b.isCompact.isClosed
  · right
    have huout : U ⊆ (interior B)ᶜ := by
      rw [← u.closure_interior]
      exact closure_minimal (fun x hx hb => hout hx (interior_subset hb))
        isOpen_interior.isClosed_compl
    apply Subset.antisymm
    · intro x hx
      refine ⟨hx.1,?_⟩
      rw [← b.frontier_eq]
      exact ⟨subset_closure hx.2,huout hx.1⟩
    · exact inter_subset_inter_right U b.boundary_subset

private theorem ball_filling_surgery_incidence
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {U T S : Set X}
    (u : ChartwisePLBall e U T) (B N C : Bool → Set X)
    (balls : ∀ i, ChartwisePLBall e (B i) (N i))
    (spheres : ∀ i, ChartwisePLSphere e (N i))
    (hdis : Disjoint (N false) (N true))
    (hcontact : ∀ i, U ∩ N i = C i)
    (hcap : ∀ i, C i ⊆ frontier U) (hcapne : ∀ i, (C i).Nonempty)
    (hcover : S ⊆ (N false ∪ N true) ∪ U) :
    (∃ i, S ⊆ B i) ∨
      (Disjoint (B false) (B true) ∧ ∀ i, U ∩ B i = C i) := by
  classical
  have hdis' (i : Bool) : Disjoint (N i) (N (!i)) := by
    cases i
    · exact hdis
    · exact hdis.symm
  have hCU (i : Bool) : C i ⊆ U := (hcontact i).symm.subset.trans inter_subset_left
  have hCN (i : Bool) : C i ⊆ N i := (hcontact i).symm.subset.trans inter_subset_right
  have hcases (i : Bool) : U ⊆ B i ∨ U ∩ B i = C i := by
    simpa only [hcontact i] using ball_contact_or_containment u (balls i)
      ((hcontact i).subset.trans (hcap i))
  by_cases hinside : ∃ i, U ⊆ B i
  · obtain ⟨i,hi⟩ := hinside
    have hnavoid : Disjoint (N (!i)) (frontier (B i)) := by
      rw [(balls i).frontier_eq]
      exact (hdis' i).symm
    have hother : N (!i) ⊆ B i := by
      rcases preconnected_interior_or_exterior_of_frontier_avoidance
        (balls i).isCompact.isClosed (spheres (!i)).isConnected.isPreconnected hnavoid with h | h
      · exact h.trans interior_subset
      · obtain ⟨x,hx⟩ := hcapne (!i)
        exact (h (hCN (!i) hx) (hi (hCU (!i) hx))).elim
    left
    refine ⟨i,hcover.trans (union_subset ?_ hi)⟩
    cases i
    · exact union_subset (balls false).boundary_subset hother
    · exact union_subset hother (balls true).boundary_subset
  · have hmeet (i : Bool) : U ∩ B i = C i := (hcases i).resolve_left
      (fun hi => hinside ⟨i,hi⟩)
    have hNout (i : Bool) : N i ⊆ (B (!i))ᶜ := by
      have hav : Disjoint (N i) (frontier (B (!i))) := by
        rw [(balls (!i)).frontier_eq]
        exact hdis' i
      rcases preconnected_interior_or_exterior_of_frontier_avoidance
        (balls (!i)).isCompact.isClosed (spheres i).isConnected.isPreconnected hav with h | h
      · obtain ⟨x,hx⟩ := hcapne i
        have hxother : x ∈ C (!i) := (hmeet (!i)).subset
          ⟨hCU i hx,interior_subset (h (hCN i hx))⟩
        exact (disjoint_left.mp (hdis' i) (hCN i hx) (hCN (!i) hxother)).elim
      · exact h
    have hBconn : IsConnected (B false) := by
      rw [← (balls false).closure_interior]
      exact (balls false).isConnected_interior.closure
    have hav : Disjoint (B false) (frontier (B true)) := by
      rw [(balls true).frontier_eq]
      exact disjoint_left.mpr (fun x hx hn => hNout true hn hx)
    have hout : B false ⊆ (B true)ᶜ := by
      rcases preconnected_interior_or_exterior_of_frontier_avoidance
        (balls true).isCompact.isClosed hBconn.isPreconnected hav with h | h
      · obtain ⟨x,hx⟩ := hcapne false
        exact (hNout false (hCN false hx)
          (interior_subset (h ((balls false).boundary_subset (hCN false hx))))).elim
      · exact h
    exact Or.inr ⟨disjoint_left.mpr (fun x hx hy => hout hx hy),hmeet⟩

theorem ChartwisePLSphere.exists_ball_of_subset_interior_ball
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R B N S : Set X}
    (he : PLDomain e R) (hR : IsCompact R)
    (b : ChartwisePLBall e B N) (hBR : B ⊆ interior R)
    (s : ChartwisePLSphere e S) (hSB : S ⊆ B) :
    ∃ A, A ⊆ R ∧ Nonempty (ChartwisePLBall e A S) := by
  obtain ⟨Q,hBQ,hQR,hQt,hQ⟩ := b.exists_enclosing_chart_in_domain hR he hBR
    isOpen_univ (subset_univ _)
  obtain ⟨A,hAQ,hA⟩ := s.exists_ball_in_compatible_unit_chart Q
    (fun x _ => he.cover x) hQ (hSB.trans hBQ) hQt
  exact ⟨A,hAQ.trans ((hQR.trans inter_subset_right).trans interior_subset),hA⟩

theorem OriginalDiskProduct.sphere_bounds_of_two_separated_cap_fillings
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R W S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e W j) (he : PLDomain e R) (hR : IsCompact R)
    (s : ChartwisePLSphere e S) (hSR : S ⊆ interior R)
    (hUR : P.closedStrip ⊆ interior R) (ret : Bool → Set X)
    (hretS : ∀ i, ret i ⊆ S)
    (hretstrip : ∀ i, ret i ∩ P.closedStrip = P.capRimSet i)
    (hretout : ∀ i, (ret i \ P.capDisk i).Nonempty)
    (hcover : (ret false ∪ ret true) ∪ P.map '' (Rim ×ˢ J) = S)
    (spheres : ∀ i, ChartwisePLSphere e (ret i ∪ P.capDisk i))
    (hdis : Disjoint (ret false ∪ P.capDisk false) (ret true ∪ P.capDisk true))
    (hfill : ∀ i, ∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B (ret i ∪ P.capDisk i))) :
    ∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B S) := by
  classical
  choose B hBR hb using fun i => hfill i
  let balls (i : Bool) : ChartwisePLBall e (B i) (ret i ∪ P.capDisk i) := Classical.choice (hb i)
  let U := P.closedStrip
  let band := P.map '' (Rim ×ˢ J)
  let N := fun i => ret i ∪ P.capDisk i
  have hcapU (i : Bool) : P.capDisk i ⊆ U := by
    apply subset_trans _ P.endDisks_subset_closedStrip
    rw [P.endDisks_eq_capDisks]
    cases i
    · exact subset_union_left
    · exact subset_union_right
  have hbandU : band ⊆ U := image_mono (prod_mono sphere_subset_closedBall subset_rfl)
  have hfront : frontier U = band ∪ (P.capDisk false ∪ P.capDisk true) := by
    rw [P.frontier_closedStrip,P.endDisks_eq_capDisks]
  have hcapfront (i : Bool) : P.capDisk i ⊆ frontier U := by
    rw [hfront]
    cases i
    · exact subset_union_of_subset_right subset_union_left _
    · exact subset_union_of_subset_right subset_union_right _
  obtain ⟨u0⟩ := P.exists_closedStrip_ball
  have hu0 : (band ∪ P.endDisks) = frontier U := by
    rw [hfront,P.endDisks_eq_capDisks]
  let u : ChartwisePLBall e U (frontier U) := hu0 ▸ u0
  have hcontact (i : Bool) : U ∩ N i = P.capDisk i := by
    apply Subset.antisymm
    · rintro x ⟨hxU,hxr | hxc⟩
      · exact P.capRimSet_subset_capDisk i ((hretstrip i).subset ⟨hxr,hxU⟩)
      · exact hxc
    · intro x hx
      exact ⟨hcapU i hx,Or.inr hx⟩
  have hcover' : S ⊆ (N false ∪ N true) ∪ U := by
    rw [← hcover]
    rintro x ((hx | hx) | hx)
    · exact Or.inl (Or.inl (Or.inl hx))
    · exact Or.inl (Or.inr (Or.inl hx))
    · exact Or.inr (hbandU hx)
  rcases ball_filling_surgery_incidence u B N P.capDisk balls spheres hdis hcontact
    hcapfront (fun i => (P.isConnected_capDisk i).nonempty) hcover' with hinside | ⟨hBdis,hmeet⟩
  · obtain ⟨i,hSi⟩ := hinside
    have hNR : N i ⊆ interior R := union_subset ((hretS i).trans hSR) ((hcapU i).trans hUR)
    exact s.exists_ball_of_subset_interior_ball he hR (balls i)
      ((balls i).subset_interior (hBR i) hNR) hSi
  · have hrimret (i : Bool) : P.capRimSet i ⊆ ret i :=
      (hretstrip i).symm.subset.trans inter_subset_left
    have hcapband (i : Bool) : P.capDisk i ∩ band = P.capRimSet i := by
      apply Subset.antisymm
      · intro x hx
        exact (P.capDisk_inter_frontier i).subset
          ⟨hx.1,(P.closedStrip_inter_frontier.symm.subset hx.2).2⟩
      · intro x hx
        have hh := (P.capDisk_inter_frontier i).symm.subset hx
        exact ⟨hh.1,P.closedStrip_inter_frontier.subset ⟨hcapU i hh.1,hh.2⟩⟩
    have hd : IsFinitePLBallPair P2 Disk Rim :=
      (isFinitePLBallPair_unit_cube (ι := Fin 2)).model_equiv
        (ContinuousLinearEquiv.ofFinrankEq (by simp) : V2 ≃L[ℝ] P2)
    have hci (i : Bool) : InjOn (P.capParameter i) Disk := by
      intro x hx y hy hxy
      exact congrArg Subtype.val ((P.embedding_capParameter i).injective
        (show (fun z : Disk => P.capParameter i z) ⟨x,hx⟩ =
          (fun z : Disk => P.capParameter i z) ⟨y,hy⟩ from hxy))
    have hNout (i : Bool) : (N i \ P.capDisk i).Nonempty := by
      obtain ⟨x,hxr,hxc⟩ := hretout i
      exact ⟨x,Or.inl hxr,hxc⟩
    have hUout : (frontier U \ P.capDisk false).Nonempty := by
      obtain ⟨x,hx⟩ := (P.isConnected_capDisk true).nonempty
      exact ⟨x,hcapfront true hx,fun h => disjoint_left.mp (P.disjoint_capDisks false) h hx⟩
    have hfirst0 := (balls false).union_of_original_disk_contact he hR u
      (hBR false) (hUR.trans interior_subset) hd (P.capParameter false)
      (P.polyhedral_capParameter false) (hci false)
      (by rw [P.capParameter_image_disk]; exact subset_union_right)
      (by rw [P.capParameter_image_disk]; exact hcapfront false)
      (by simpa only [P.capParameter_image_disk] using hNout false)
      (by simpa only [P.capParameter_image_disk] using hUout)
      (by rw [P.capParameter_image_disk,inter_comm]; exact hmeet false)
    rw [P.capParameter_image_disk,P.capParameter_image_rim] at hfirst0
    have hfirstfront :
        (N false \ (P.capDisk false \ P.capRimSet false)) ∪
          (frontier U \ (P.capDisk false \ P.capRimSet false)) =
        (ret false ∪ band) ∪ P.capDisk true := by
      rw [hfront]
      ext x
      have hr : x ∈ P.capRimSet false → x ∈ ret false := fun h => hrimret false h
      have hb : x ∈ band → x ∈ P.capDisk false → x ∈ P.capRimSet false :=
        fun hb hc => (hcapband false).subset ⟨hc,hb⟩
      have ht : x ∈ ret false → x ∈ P.capDisk false → x ∈ P.capRimSet false :=
        fun hr hc => (hretstrip false).subset ⟨hr,hcapU false hc⟩
      have hd' : ¬ (x ∈ P.capDisk false ∧ x ∈ P.capDisk true) :=
        fun h => disjoint_left.mp (P.disjoint_capDisks false) h.1 h.2
      change (((x ∈ ret false ∨ x ∈ P.capDisk false) ∧
          ¬(x ∈ P.capDisk false ∧ x ∉ P.capRimSet false)) ∨
        ((x ∈ band ∨ x ∈ P.capDisk false ∨ x ∈ P.capDisk true) ∧
          ¬(x ∈ P.capDisk false ∧ x ∉ P.capRimSet false))) ↔
        ((x ∈ ret false ∨ x ∈ band) ∨ x ∈ P.capDisk true)
      tauto
    rw [hfirstfront] at hfirst0
    obtain ⟨first⟩ := hfirst0
    have hfirstR : B false ∪ U ⊆ R := union_subset (hBR false) (hUR.trans interior_subset)
    have hfirstout : (((ret false ∪ band) ∪ P.capDisk true) \ P.capDisk true).Nonempty := by
      obtain ⟨x,hxr,_⟩ := hretout false
      exact ⟨x,Or.inl (Or.inl hxr),fun h => disjoint_left.mp hdis (Or.inl hxr) (Or.inr h)⟩
    have hsecond0 := first.union_of_original_disk_contact he hR (balls true)
      hfirstR (hBR true) hd (P.capParameter true) (P.polyhedral_capParameter true) (hci true)
      (by rw [P.capParameter_image_disk]; exact subset_union_right)
      (by rw [P.capParameter_image_disk]; exact subset_union_right)
      (by simpa only [P.capParameter_image_disk] using hfirstout)
      (by simpa only [P.capParameter_image_disk] using hNout true)
      (by
        rw [P.capParameter_image_disk]
        apply Subset.antisymm
        · rintro x ⟨hx | hx,hy⟩
          · exact (disjoint_left.mp hBdis hx hy).elim
          · exact (hmeet true).subset ⟨hx,hy⟩
        · intro x hx
          have h := (hmeet true).symm.subset hx
          exact ⟨Or.inr h.1,h.2⟩)
    rw [P.capParameter_image_disk,P.capParameter_image_rim] at hsecond0
    have hsecondfront :
        (((ret false ∪ band) ∪ P.capDisk true) \ (P.capDisk true \ P.capRimSet true)) ∪
          (N true \ (P.capDisk true \ P.capRimSet true)) = S := by
      rw [← hcover]
      ext x
      have hr : x ∈ P.capRimSet true → x ∈ ret true := fun h => hrimret true h
      have hb : x ∈ band → x ∈ P.capDisk true → x ∈ P.capRimSet true :=
        fun hb hc => (hcapband true).subset ⟨hc,hb⟩
      have ht : x ∈ ret true → x ∈ P.capDisk true → x ∈ P.capRimSet true :=
        fun hr hc => (hretstrip true).subset ⟨hr,hcapU true hc⟩
      have hd' : ¬ (x ∈ ret false ∧ x ∈ P.capDisk true) :=
        fun h => disjoint_left.mp hdis (Or.inl h.1) (Or.inr h.2)
      change ((((x ∈ ret false ∨ x ∈ band) ∨ x ∈ P.capDisk true) ∧
          ¬(x ∈ P.capDisk true ∧ x ∉ P.capRimSet true)) ∨
        ((x ∈ ret true ∨ x ∈ P.capDisk true) ∧
          ¬(x ∈ P.capDisk true ∧ x ∉ P.capRimSet true))) ↔
        ((x ∈ ret false ∨ x ∈ ret true) ∨ x ∈ band)
      tauto
    rw [hsecondfront] at hsecond0
    exact ⟨(B false ∪ U) ∪ B true,union_subset hfirstR (hBR true),hsecond0⟩

theorem ChartwisePLSphere.exists_original_nonbounding_disk_surgery
    {X ι E : Type*} [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {R S V : Set X} {d q : Set E}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R)
    (hn : ¬ ∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B S))
    (hd : IsFinitePLBallPair P2 d q) (j : E → X)
    (hj : PolyhedralPLInCharts e j d) (hji : InjOn j d)
    (hjR : MapsTo j d (interior R)) (hproper : ∀ z ∈ d, j z ∈ S ↔ z ∈ q)
    (hV : IsOpen V) (hjV : j '' d ⊆ V) :
    ∃ (K : Set X) (k : V2 → X) (P : OriginalDiskProduct e (R ∩ (interior K)ᶜ) k)
      (a r : Bool → Set V3),
      IsCompact K ∧ PLDomain e K ∧ k '' Disk = j '' d ∧ k '' Rim = j '' q ∧
      MapsTo P.map (Disk ×ˢ Icc (-1 : ℝ) 1) (V ∩ interior R) ∧
      (∀ z ∈ Disk ×ˢ Icc (-1 : ℝ) 1, P.map z ∈ S ↔ z.1 ∈ Rim) ∧
      (∀ b, IsFinitePLBallPair P2 (a b) (r b) ∧ a b ⊆ Sphere ∧
        IsFinitePLBallPair P2 (Sphere \ (a b \ r b)) (r b) ∧
        s.map '' r b = P.capRimSet b ∧ (s.map '' a b) ∩ P.closedStrip = s.map '' r b) ∧
      ∃ t : ∀ b, ChartwisePLSphere e ((s.map '' a b) ∪ P.capDisk b),
        (∀ b, EqOn (t b).map s.map (a b) ∧
          (t b).map '' (Sphere \ (a b \ r b)) = P.capDisk b) ∧
        Disjoint ((s.map '' a true) ∪ P.capDisk true)
          ((s.map '' a false) ∪ P.capDisk false) ∧
        (((s.map '' a true) ∪ P.capDisk true) ∪
          ((s.map '' a false) ∪ P.capDisk false)) \ P.closedStrip = S \ P.closedStrip ∧
        (∀ b, (s.map '' a b) ∪ P.capDisk b ⊆ interior R) ∧
        ∃ b, ¬ ∃ B, B ⊆ R ∧
          Nonempty (ChartwisePLBall e B ((s.map '' a b) ∪ P.capDisk b)) := by
  classical
  obtain ⟨K,_,_,k,hK,hKPL,_,_,_,_,_,_,_,_,hkD,hkQ,_,_,P,hP,hPS,_,_,_,_⟩ :=
    s.exists_original_whole_disk_product hR he hSR isOpen_univ (subset_univ S)
      hd j hj hji hjR hproper hV hjV
  obtain ⟨a,r,har,_,hcover,t,ht,hdis,houtside⟩ :=
    P.exists_original_separated_end_spheres s he.compatible hPS
  have hcapU (b : Bool) : P.capDisk b ⊆ P.closedStrip := by
    apply subset_trans _ P.endDisks_subset_closedStrip
    rw [P.endDisks_eq_capDisks]
    cases b
    · exact subset_union_left
    · exact subset_union_right
  have hUR : P.closedStrip ⊆ interior R := by
    rintro _ ⟨z,hz,rfl⟩
    exact (hP ⟨hz.1,by constructor <;> linarith [hz.2.1,hz.2.2]⟩).1.2
  have hretS (b : Bool) : s.map '' a b ⊆ S := by
    rintro _ ⟨z,hz,rfl⟩
    rw [s.map_eq ⟨z,(har b).2.1 hz⟩]
    exact (s.parametrization ⟨z,(har b).2.1 hz⟩).property
  have hNR (b : Bool) : (s.map '' a b) ∪ P.capDisk b ⊆ interior R :=
    union_subset ((hretS b).trans hSR) ((hcapU b).trans hUR)
  have hretstrip (b : Bool) : (s.map '' a b) ∩ P.closedStrip = P.capRimSet b :=
    (har b).2.2.2.2.trans (har b).2.2.2.1
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hretout (b : Bool) : ((s.map '' a b) \ P.capDisk b).Nonempty := by
    obtain ⟨z,hza,hzr⟩ := (har b).1.sdiff_nonempty
    refine ⟨s.map z,⟨z,hza,rfl⟩,?_⟩
    intro hc
    have hr : s.map z ∈ s.map '' r b :=
      (har b).2.2.2.2.subset ⟨⟨z,hza,rfl⟩,hcapU b hc⟩
    obtain ⟨w,hwr,hwz⟩ := hr
    exact hzr (hsi ((har b).2.1 ((har b).1.1 hwr)) ((har b).2.1 hza) hwz ▸ hwr)
  refine ⟨K,k,P,a,r,hK,hKPL,hkD,hkQ,fun z hz => (hP hz).1,hPS,har,
    t,ht,hdis,houtside,hNR,?_⟩
  by_contra h
  push Not at h
  apply hn
  apply P.sphere_bounds_of_two_separated_cap_fillings he hR s hSR hUR
    (fun b => s.map '' a b) hretS hretstrip hretout _ t hdis.symm h
  simpa only [union_comm (s.map '' a true) (s.map '' a false)] using hcover

end PoincareConjecture.M76
