find_package(Z3 CONFIG REQUIRED)

add_executable(solver_opensmt_z3 ../main.cpp SolverProcess.cpp)

target_include_directories(solver_opensmt_z3 PRIVATE ${Z3_CXX_INCLUDE_DIRS})
target_link_libraries(solver_opensmt_z3 client ${GMP_LIBRARY} ${GMPXX_LIBRARY} ${Z3_LIBRARIES})

if (VERBOSE_THREAD)
    target_compile_definitions(solver_opensmt_z3 PUBLIC -DVERBOSE_THREAD)
endif()
