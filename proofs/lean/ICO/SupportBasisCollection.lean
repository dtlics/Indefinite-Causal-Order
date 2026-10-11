import ICO.SupportBasisRows.Row0
import ICO.SupportBasisRows.Row1
import ICO.SupportBasisRows.Row2
import ICO.SupportBasisRows.Row3
import ICO.SupportBasisRows.Row4
import ICO.SupportBasisRows.Row5
import ICO.SupportBasisRows.Row6
import ICO.SupportBasisRows.Row7
import ICO.SupportBasisRows.Row8
import ICO.SupportBasisRows.Row9
import ICO.SupportBasisRows.Row10
import ICO.SupportBasisRows.Row11
import ICO.SupportBasisRows.Row12
import ICO.SupportBasisRows.Row13
import ICO.SupportBasisRows.Row14
import ICO.SupportBasisRows.Row15
import ICO.SupportBasisRows.Row16
import ICO.SupportBasisRows.Row17
import ICO.SupportBasisRows.Row18
import ICO.SupportBasisRows.Row19
import ICO.SupportBasisRows.Row20
import ICO.SupportBasisRows.Row21
import ICO.SupportBasisRows.Row22
import ICO.SupportBasisRows.Row23
import ICO.SupportBasisRows.Row24
import ICO.SupportBasisRows.Row25
import ICO.SupportBasisRows.Row26
import ICO.SupportBasisRows.Row27
import ICO.SupportBasisRows.Row28
import ICO.SupportBasisRows.Row29
import ICO.SupportBasisRows.Row30
import ICO.SupportBasisRows.Row31
import ICO.SupportBasisRows.Row32
import ICO.SupportBasisRows.Row33
import ICO.SupportBasisRows.Row34
import ICO.SupportBasisRows.Row35
import ICO.SupportBasisRows.Row36
import ICO.SupportBasisRows.Row37
import ICO.SupportBasisRows.Row38
import ICO.SupportBasisRows.Row39
import ICO.SupportBasisRows.Row40
import ICO.SupportBasisRows.Row41
import ICO.SupportBasisRows.Row42
import ICO.SupportBasisRows.Row43
import ICO.SupportBasisRows.Row44
import ICO.SupportBasisRows.Row45
import ICO.SupportBasisRows.Row46
import ICO.SupportBasisRows.Row47
import ICO.SupportBasisRows.Row48
import ICO.SupportBasisRows.Row49
import ICO.SupportBasisRows.Row50
import ICO.SupportBasisRows.Row51
import ICO.SupportBasisRows.Row52
import ICO.SupportBasisRows.Row53
import ICO.SupportBasisRows.Row54
import ICO.SupportBasisRows.Row55
import ICO.SupportBasisRows.Row56
import ICO.SupportBasisRows.Row57
import ICO.SupportBasisRows.Row58
import ICO.SupportBasisRows.Row59
import ICO.SupportBasisRows.Row60
import ICO.SupportBasisRows.Row61
import ICO.SupportBasisRows.Row62
import ICO.SupportBasisRows.Row63
import ICO.SupportBasisRows.Row64
import ICO.SupportBasisRows.Row65
import ICO.SupportBasisRows.Row66
import ICO.SupportBasisRows.Row67
import ICO.SupportBasisRows.Row68
import ICO.SupportBasisRows.Row69
import ICO.SupportBasisRows.Row70
import ICO.SupportBasisRows.Row71
import ICO.SupportBasisRows.Row72
import ICO.SupportBasisRows.Row73
import ICO.SupportBasisRows.Row74
import ICO.SupportBasisRows.Row75
import ICO.SupportBasisRows.Row76
import ICO.SupportBasisRows.Row77
import ICO.SupportBasisRows.Row78
import ICO.SupportBasisRows.Row79
import ICO.SupportBasisRows.Row80
import ICO.SupportBasisRows.Row81
import ICO.SupportBasisRows.Row82
import ICO.SupportBasisRows.Row83
import ICO.SupportBasisRows.Row84
import ICO.SupportBasisRows.Row85
import ICO.SupportBasisRows.Row86
import ICO.SupportBasisRows.Row87
import ICO.SupportBasisRows.Row88
import ICO.SupportBasisRows.Row89
import ICO.SupportBasisRows.Row90
import ICO.SupportBasisRows.Row91
import ICO.SupportBasisRows.Row92
import ICO.SupportBasisRows.Row93
import ICO.SupportBasisRows.Row94
import ICO.SupportBasisRows.Row95
import ICO.SupportBasisRows.Row96
import ICO.SupportBasisRows.Row97
import ICO.SupportBasisRows.Row98
import ICO.SupportBasisRows.Row99
import ICO.SupportBasisRows.Row100
import ICO.SupportBasisRows.Row101
import ICO.SupportBasisRows.Row102
import ICO.SupportBasisRows.Row103
import ICO.SupportBasisRows.Row104
import ICO.SupportBasisRows.Row105
import ICO.SupportBasisRows.Row106
import ICO.SupportBasisRows.Row107
import ICO.SupportBasisRows.Row108
import ICO.SupportBasisRows.Row109
import ICO.SupportBasisRows.Row110
import ICO.SupportBasisRows.Row111
import ICO.SupportBasisRows.Row112
import ICO.SupportBasisRows.Row113
import ICO.SupportBasisRows.Row114
import ICO.SupportBasisRows.Row115
import ICO.SupportBasisRows.Row116
import ICO.SupportBasisRows.Row117
import ICO.SupportBasisRows.Row118
import ICO.SupportBasisRows.Row119
import ICO.SupportBasisRows.Row120
import ICO.SupportBasisRows.Row121
import ICO.SupportBasisRows.Row122
import ICO.SupportBasisRows.Row123
import ICO.SupportBasisRows.Row124
import ICO.SupportBasisRows.Row125
import ICO.SupportBasisRows.Row126
import ICO.SupportBasisRows.Row127
namespace ICO.SupportModularTree
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem all_basis_entries (r : Fin 128) (b : Fin 25) :
    basisProductRe r.val b.val = (if r.val = 103+b.val then 1 else 0) ∧
    basisProductIm r.val b.val = 0 := by
  match r with
  | ⟨0, _⟩ => exact basis_row_0 b
  | ⟨1, _⟩ => exact basis_row_1 b
  | ⟨2, _⟩ => exact basis_row_2 b
  | ⟨3, _⟩ => exact basis_row_3 b
  | ⟨4, _⟩ => exact basis_row_4 b
  | ⟨5, _⟩ => exact basis_row_5 b
  | ⟨6, _⟩ => exact basis_row_6 b
  | ⟨7, _⟩ => exact basis_row_7 b
  | ⟨8, _⟩ => exact basis_row_8 b
  | ⟨9, _⟩ => exact basis_row_9 b
  | ⟨10, _⟩ => exact basis_row_10 b
  | ⟨11, _⟩ => exact basis_row_11 b
  | ⟨12, _⟩ => exact basis_row_12 b
  | ⟨13, _⟩ => exact basis_row_13 b
  | ⟨14, _⟩ => exact basis_row_14 b
  | ⟨15, _⟩ => exact basis_row_15 b
  | ⟨16, _⟩ => exact basis_row_16 b
  | ⟨17, _⟩ => exact basis_row_17 b
  | ⟨18, _⟩ => exact basis_row_18 b
  | ⟨19, _⟩ => exact basis_row_19 b
  | ⟨20, _⟩ => exact basis_row_20 b
  | ⟨21, _⟩ => exact basis_row_21 b
  | ⟨22, _⟩ => exact basis_row_22 b
  | ⟨23, _⟩ => exact basis_row_23 b
  | ⟨24, _⟩ => exact basis_row_24 b
  | ⟨25, _⟩ => exact basis_row_25 b
  | ⟨26, _⟩ => exact basis_row_26 b
  | ⟨27, _⟩ => exact basis_row_27 b
  | ⟨28, _⟩ => exact basis_row_28 b
  | ⟨29, _⟩ => exact basis_row_29 b
  | ⟨30, _⟩ => exact basis_row_30 b
  | ⟨31, _⟩ => exact basis_row_31 b
  | ⟨32, _⟩ => exact basis_row_32 b
  | ⟨33, _⟩ => exact basis_row_33 b
  | ⟨34, _⟩ => exact basis_row_34 b
  | ⟨35, _⟩ => exact basis_row_35 b
  | ⟨36, _⟩ => exact basis_row_36 b
  | ⟨37, _⟩ => exact basis_row_37 b
  | ⟨38, _⟩ => exact basis_row_38 b
  | ⟨39, _⟩ => exact basis_row_39 b
  | ⟨40, _⟩ => exact basis_row_40 b
  | ⟨41, _⟩ => exact basis_row_41 b
  | ⟨42, _⟩ => exact basis_row_42 b
  | ⟨43, _⟩ => exact basis_row_43 b
  | ⟨44, _⟩ => exact basis_row_44 b
  | ⟨45, _⟩ => exact basis_row_45 b
  | ⟨46, _⟩ => exact basis_row_46 b
  | ⟨47, _⟩ => exact basis_row_47 b
  | ⟨48, _⟩ => exact basis_row_48 b
  | ⟨49, _⟩ => exact basis_row_49 b
  | ⟨50, _⟩ => exact basis_row_50 b
  | ⟨51, _⟩ => exact basis_row_51 b
  | ⟨52, _⟩ => exact basis_row_52 b
  | ⟨53, _⟩ => exact basis_row_53 b
  | ⟨54, _⟩ => exact basis_row_54 b
  | ⟨55, _⟩ => exact basis_row_55 b
  | ⟨56, _⟩ => exact basis_row_56 b
  | ⟨57, _⟩ => exact basis_row_57 b
  | ⟨58, _⟩ => exact basis_row_58 b
  | ⟨59, _⟩ => exact basis_row_59 b
  | ⟨60, _⟩ => exact basis_row_60 b
  | ⟨61, _⟩ => exact basis_row_61 b
  | ⟨62, _⟩ => exact basis_row_62 b
  | ⟨63, _⟩ => exact basis_row_63 b
  | ⟨64, _⟩ => exact basis_row_64 b
  | ⟨65, _⟩ => exact basis_row_65 b
  | ⟨66, _⟩ => exact basis_row_66 b
  | ⟨67, _⟩ => exact basis_row_67 b
  | ⟨68, _⟩ => exact basis_row_68 b
  | ⟨69, _⟩ => exact basis_row_69 b
  | ⟨70, _⟩ => exact basis_row_70 b
  | ⟨71, _⟩ => exact basis_row_71 b
  | ⟨72, _⟩ => exact basis_row_72 b
  | ⟨73, _⟩ => exact basis_row_73 b
  | ⟨74, _⟩ => exact basis_row_74 b
  | ⟨75, _⟩ => exact basis_row_75 b
  | ⟨76, _⟩ => exact basis_row_76 b
  | ⟨77, _⟩ => exact basis_row_77 b
  | ⟨78, _⟩ => exact basis_row_78 b
  | ⟨79, _⟩ => exact basis_row_79 b
  | ⟨80, _⟩ => exact basis_row_80 b
  | ⟨81, _⟩ => exact basis_row_81 b
  | ⟨82, _⟩ => exact basis_row_82 b
  | ⟨83, _⟩ => exact basis_row_83 b
  | ⟨84, _⟩ => exact basis_row_84 b
  | ⟨85, _⟩ => exact basis_row_85 b
  | ⟨86, _⟩ => exact basis_row_86 b
  | ⟨87, _⟩ => exact basis_row_87 b
  | ⟨88, _⟩ => exact basis_row_88 b
  | ⟨89, _⟩ => exact basis_row_89 b
  | ⟨90, _⟩ => exact basis_row_90 b
  | ⟨91, _⟩ => exact basis_row_91 b
  | ⟨92, _⟩ => exact basis_row_92 b
  | ⟨93, _⟩ => exact basis_row_93 b
  | ⟨94, _⟩ => exact basis_row_94 b
  | ⟨95, _⟩ => exact basis_row_95 b
  | ⟨96, _⟩ => exact basis_row_96 b
  | ⟨97, _⟩ => exact basis_row_97 b
  | ⟨98, _⟩ => exact basis_row_98 b
  | ⟨99, _⟩ => exact basis_row_99 b
  | ⟨100, _⟩ => exact basis_row_100 b
  | ⟨101, _⟩ => exact basis_row_101 b
  | ⟨102, _⟩ => exact basis_row_102 b
  | ⟨103, _⟩ => exact basis_row_103 b
  | ⟨104, _⟩ => exact basis_row_104 b
  | ⟨105, _⟩ => exact basis_row_105 b
  | ⟨106, _⟩ => exact basis_row_106 b
  | ⟨107, _⟩ => exact basis_row_107 b
  | ⟨108, _⟩ => exact basis_row_108 b
  | ⟨109, _⟩ => exact basis_row_109 b
  | ⟨110, _⟩ => exact basis_row_110 b
  | ⟨111, _⟩ => exact basis_row_111 b
  | ⟨112, _⟩ => exact basis_row_112 b
  | ⟨113, _⟩ => exact basis_row_113 b
  | ⟨114, _⟩ => exact basis_row_114 b
  | ⟨115, _⟩ => exact basis_row_115 b
  | ⟨116, _⟩ => exact basis_row_116 b
  | ⟨117, _⟩ => exact basis_row_117 b
  | ⟨118, _⟩ => exact basis_row_118 b
  | ⟨119, _⟩ => exact basis_row_119 b
  | ⟨120, _⟩ => exact basis_row_120 b
  | ⟨121, _⟩ => exact basis_row_121 b
  | ⟨122, _⟩ => exact basis_row_122 b
  | ⟨123, _⟩ => exact basis_row_123 b
  | ⟨124, _⟩ => exact basis_row_124 b
  | ⟨125, _⟩ => exact basis_row_125 b
  | ⟨126, _⟩ => exact basis_row_126 b
  | ⟨127, _⟩ => exact basis_row_127 b
  | ⟨Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (n)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), h⟩ => omega
end ICO.SupportModularTree
