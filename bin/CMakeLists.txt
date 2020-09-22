add_executable( GSInserter

        GSInserter.cpp

        )



target_compile_features(GSInserter PRIVATE cxx_range_for cxx_auto_type)



target_link_libraries( GSInserter

        clangFrontend

        clangSerialization

        clangDriver

        clangParse

        clangSema

        clangAnalysis

        clangAST

        clangBasic

        clangEdit

        clangLex

        clangTooling

        clangASTMatchers

        clangDriver

        clangFrontendTool

        clangLex

        clangParse

        clangSema

        clangRewrite

        clangRewriteFrontend

        clangStaticAnalyzerFrontend

        clangStaticAnalyzerCheckers

        clangStaticAnalyzerCore

        clangCrossTU

        clangIndex

        clangToolingCore

        clangFormat

        )



target_link_libraries( GSInserter

        LLVMX86AsmParser # MC, MCParser, Support, X86Desc, X86Info

        LLVMX86Desc # MC, Support, X86AsmPrinter, X86Info

        LLVMX86AsmPrinter # MC, Support, X86Utils

        LLVMX86Info # MC, Support, Target

        LLVMX86Utils # Core, Support

        LLVMipo

        LLVMScalarOpts

        LLVMInstCombine

        LLVMTransformUtils

        #LLVMipa

        LLVMAnalysis

        LLVMTarget

        LLVMOption # Support

        LLVMMCParser # MC, Support

        LLVMMC # Object, Support

        LLVMObject # BitReader, Core, Support

        LLVMBitReader # Core, Support

        LLVMCore # Support

        LLVMSupport

        )





# LLVM is (typically) built with no C++ RTTI. We need to match that;

# otherwise, we'll get linker errors about missing RTTI data.

set_target_properties(GSInserter PROPERTIES

        COMPILE_FLAGS "-fno-rtti -g"

        )
