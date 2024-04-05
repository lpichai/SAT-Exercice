(define (domain logistics)
    (:requirements :strips :typing)
    (:types
        robot - agent
        room - location
    )
    (:predicates
        (robot_at ?robot - robot ?room - location)
    )
    (:action move
        :parameters (?robot - robot ?room1 - location ?room2 - location)
        :precondition (
            and(robot_at ?robot ?room1)
        )
        :effect (
            and (robot_at ?robot ?room2) (not (robot_at ?robot ?room1))
        )
    )
)
