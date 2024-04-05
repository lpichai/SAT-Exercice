(define (problem p01)
    (:domain logistics)
    (:objects
    robot1 robot2 robot3 robot4 - robot
    room1 room2 - room
  )

  (:init
    ;;Operation schedule
    (robot_at robot1 room1)
    (robot_at robot2 room1)
    (robot_at robot3 room1)
    (robot_at robot4 room2)
  )

  (:goal
    (and (robot_at robot1 room2)
    (robot_at robot2 room2)
    (robot_at robot3 room2)
    (robot_at robot4 room2))
  )
)