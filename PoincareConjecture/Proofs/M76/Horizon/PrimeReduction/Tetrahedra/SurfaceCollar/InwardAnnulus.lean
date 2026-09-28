import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.AnnulusSides









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Sphere" => sphere (0 : V3) 1

theorem ChartwisePLSphere.exists_inward_annulus_of_parameter_cut
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S R O : Set X}
    (s : ChartwisePLSphere e S) (d : Fin 2 → Set V3) {r : Set V3}
    (hd : ∀ i, IsFinitePLBallPair P2 (d i) r)
    (hwhole : d 0 ∪ d 1 = Sphere) (hinter : d 0 ∩ d 1 = r)
    (hO : IsOpen O) (hrO : s.map '' r ⊆ O)
    (hrfront : s.map '' r ⊆ frontier R)
    (hisolate : (S ∩ O) ∩ frontier R ⊆ s.map '' r)
    (hinward : (s.map '' r ∩ closure (S ∩ interior R)).Nonempty) :
    ∃ (i : Fin 2) (a : ℝ) (f : P2 → V3) (k q b : Set V3),
      0 < a ∧ a < 1 ∧
      FinitePiecewiseAffineOn f (closedBall (0 : P2) 1) ∧
      InjOn f (closedBall (0 : P2) 1) ∧
      f '' closedBall (0 : P2) 1 = d i ∧ f '' sphere (0 : P2) 1 = r ∧
      k = f '' closedBall (0 : P2) a ∧ q = f '' sphere (0 : P2) a ∧
      b = f '' {x : P2 | ‖x‖ ∈ Icc a 1} ∧
      IsFinitePLBallPair P2 k q ∧ k ∪ b = d i ∧ k ∩ b = q ∧
      Disjoint k r ∧ r ⊆ b ∧
      s.map '' b ⊆ S ∩ O ∧ PolyhedralPLInCharts e s.map b ∧
      PolyhedralPLInCharts e (s.map ∘ f) (closedBall (0 : P2) 1) ∧
      (s.map '' b) \ (s.map '' r) ⊆ interior R ∧
      s.map '' q ⊆ interior R ∧
      ∃ H : {x : P2 | ‖x‖ ∈ Icc a 1} ≃ₜ b,
        H.IsFinitePL ∧ (∀ x, (H x : V3) = f x) := by
  classical
  obtain ⟨a,f,k,q,b,hdata,_,_,_,_,hcover⟩ :=
    s.exists_separated_retained_circle_disks d hd hwhole hinter hO hrO
  choose ha ha1 hf hfi hfd hfr hk hq hb hkp hkb hkbi hkr hrb hbO hkPL hbPL hsf H hH hHval
    using hdata
  have hdS (i : Fin 2) : d i ⊆ Sphere := by
    fin_cases i
    · exact subset_union_left.trans hwhole.subset
    · exact subset_union_right.trans hwhole.subset
  have hks (i) : k i ⊆ Sphere := (subset_union_left.trans (hkb i).subset).trans (hdS i)
  have hbs (i) : b i ⊆ Sphere := (subset_union_right.trans (hkb i).subset).trans (hdS i)
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hrS : r ⊆ Sphere := (hd 0).1.trans (hdS 0)
  have hmapS (x : V3) (hx : x ∈ Sphere) : s.map x ∈ S := by
    rw [s.map_eq ⟨x,hx⟩]
    exact (s.parametrization ⟨x,hx⟩).property
  have hbc (i) : IsConnected ((s.map '' b i) \ (s.map '' r)) := by
    have hc : IsConnected (b i \ r) := by
      rw [hb i,←hfr i]
      exact isConnected_retained_annulus_without_rim (ha i) (ha1 i)
        (hf i).continuousOn (hfi i)
    rw [←Set.InjOn.image_sdiff_subset (hsi.mono (hbs i)) (hrb i)]
    exact hc.image _ (s.piecewiseAffine.continuousOn.mono (sdiff_subset.trans (hbs i)))
  have hkclosed (i) : IsClosed (s.map '' k i) :=
    ((hkp i).isCompact.image_of_continuousOn (hkPL i).continuousOn).isClosed
  obtain ⟨x,hxr,hxcl⟩ := hinward
  have hxnot (i) : x ∉ s.map '' k i := by
    rintro ⟨z,hz,hzx⟩
    obtain ⟨y,hy,hyx⟩ := hxr
    have heq := hsi (hks i hz) (hrS hy) (hzx.trans hyx.symm)
    exact disjoint_left.mp (hkr i) hz (heq.symm ▸ hy)
  let U := ((s.map '' k 0) ∪ (s.map '' k 1))ᶜ
  have hU : IsOpen U := ((hkclosed 0).union (hkclosed 1)).isOpen_compl
  have hxU : x ∈ U := fun h => h.elim (hxnot 0) (hxnot 1)
  obtain ⟨y,hyU,hyS,hyR⟩ := mem_closure_iff.mp hxcl U hU hxU
  have hyb : ∃ i : Fin 2, y ∈ s.map '' b i := by
    have hc := hcover.symm.subset hyS
    rcases hc with (hy | hy) | (hy | hy)
    · exact False.elim (hyU (Or.inl hy))
    · exact ⟨0,hy⟩
    · exact False.elim (hyU (Or.inr hy))
    · exact ⟨1,hy⟩
  obtain ⟨i,hyi⟩ := hyb
  have hyr : y ∉ s.map '' r := fun h => (hrfront h).2 hyR
  have hbin : (s.map '' b i) \ (s.map '' r) ⊆ interior R := by
    apply (hbc i).isPreconnected.subset_interior_of_avoids_frontier
      (hmeet := ⟨y,⟨hyi,hyr⟩,hyR⟩)
    apply disjoint_left.mpr
    rintro z ⟨hz,hzr⟩ hzfront
    obtain ⟨w,hw,rfl⟩ := hz
    exact hzr (hisolate ⟨⟨hmapS w (hbs i hw),hbO i ⟨w,hw,rfl⟩⟩,hzfront⟩)
  refine ⟨i,a i,f i,k i,q i,b i,ha i,ha1 i,hf i,hfi i,hfd i,hfr i,
    hk i,hq i,hb i,hkp i,hkb i,hkbi i,hkr i,hrb i,?_,hbPL i,hsf i,hbin,?_,H i,hH i,hHval i⟩
  · rintro z ⟨w,hw,rfl⟩
    exact ⟨hmapS w (hbs i hw),hbO i ⟨w,hw,rfl⟩⟩
  · rintro z ⟨w,hw,rfl⟩
    have hwkb := (hkbi i).symm.subset hw
    apply hbin ⟨⟨w,hwkb.2,rfl⟩,?_⟩
    rintro ⟨v,hv,hvw⟩
    have heq := hsi (hrS hv) (hks i hwkb.1) hvw
    exact disjoint_left.mp (hkr i) hwkb.1 (heq ▸ hv)

end PoincareConjecture.M76
