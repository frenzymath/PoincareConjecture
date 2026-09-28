import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.TwoSidedRimNeighborhood










set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Sphere" => sphere (0 : V3) 1

theorem ChartwisePLSphere.disk_side_eq_of_inward_shell
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S R U : Set X}
    (s : ChartwisePLSphere e S) (d : Fin 2 → Set V3) {r : Set V3}
    (hd : ∀ i, IsFinitePLBallPair P2 (d i) r)
    (hwhole : d 0 ∪ d 1 = Sphere) (hinter : d 0 ∩ d 1 = r)
    (i j : Fin 2) (hU : IsOpen U) (hrU : s.map '' r ⊆ U)
    (hi : (S ∩ R) ∩ U ⊆ s.map '' d i)
    {k b : Set V3} (hkc : IsClosed (s.map '' k))
    (hkr : Disjoint (s.map '' k) (s.map '' r)) (hkb : k ∪ b = d j)
    (hbR : s.map '' b ⊆ R) (hrne : (s.map '' r).Nonempty) : j = i := by
  have hdS (l : Fin 2) : d l ⊆ Sphere := by
    fin_cases l
    · exact subset_union_left.trans hwhole.subset
    · exact subset_union_right.trans hwhole.subset
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hmapS (x : V3) (hx : x ∈ Sphere) : s.map x ∈ S := by
    rw [s.map_eq ⟨x,hx⟩]
    exact (s.parametrization ⟨x,hx⟩).property
  obtain ⟨x,hxr⟩ := hrne
  have hxclosure : x ∈ closure (s.map '' (d j \ r)) := by
    have hc : ContinuousOn s.map (closure (d j \ r)) := by
      rw [(hd j).closure_sdiff]
      exact s.piecewiseAffine.continuousOn.mono (hdS j)
    apply hc.image_closure
    rw [(hd j).closure_sdiff]
    exact image_mono (hd j).1 hxr
  obtain ⟨y,hyU,hy⟩ := mem_closure_iff.mp hxclosure (U ∩ (s.map '' k)ᶜ)
    (hU.inter hkc.isOpen_compl)
    ⟨hrU hxr,fun h => disjoint_left.mp hkr h hxr⟩
  obtain ⟨z,hz,hzy⟩ := hy
  have hyb : y ∈ s.map '' b := by
    rcases hkb.symm.subset hz.1 with hk | hb
    · exact (hyU.2 ⟨z,hk,hzy⟩).elim
    · exact ⟨z,hb,hzy⟩
  have hyS : y ∈ S := hzy ▸ hmapS z (hdS j hz.1)
  have hyi : y ∈ s.map '' d i := hi ⟨⟨hyS,hbR hyb⟩,hyU.1⟩
  by_contra hji
  have hji' : j = i.rev := by fin_cases i <;> fin_cases j <;> simp_all
  have hdd : d j ∩ d i = r := by
    rw [hji']
    fin_cases i
    · exact (inter_comm _ _).trans hinter
    · exact hinter
  have hyr : y ∈ s.map '' r := by
    rw [←hdd,hsi.image_inter (hdS j) (hdS i)]
    exact ⟨⟨z,hz.1,hzy⟩,hyi⟩
  obtain ⟨w,hw,hwy⟩ := hyr
  exact hz.2 ((hsi ((hd 0).1.trans (hdS 0) hw) (hdS j hz.1)
    (hwy.trans hzy.symm)) ▸ hw)

end PoincareConjecture.M76
