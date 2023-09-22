file(GLOB_RECURSE SOURCES *.cpp)

add_executable(${PROJECT_NAME} ${SOURCES})
target_link_libraries(${PROJECT_NAME} minisat::minisat)
target_include_directories(${PROJECT_NAME} PUBLIC ${INCLUDE_DIR})